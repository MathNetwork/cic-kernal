'use client'

import { useState, useMemo, useRef, useEffect, useCallback } from 'react'
import { forceSimulation, forceLink, forceManyBody, forceCenter, forceCollide, type SimulationNodeDatum } from 'd3-force'
import { zoom, zoomIdentity } from 'd3-zoom'
import { drag } from 'd3-drag'
import { select } from 'd3-selection'
import { hierarchy, tree as d3tree } from 'd3-hierarchy'
import treeData from './data/treeenv.json'
import hyperData from './data/cahypergraph.json'

// ── Types ──
type TreeNode = { tag: string; hash: number; step: number; children: TreeNode[]; name?: string; index?: number; level?: string; levels?: string[] }
type Decl = { name: string; kind: string; type: TreeNode; value: TreeNode | null }
type Nerve = { hash: number; ref: number[]; record: string; step: number; decl: string; phase: string }
interface SimNode extends SimulationNodeDatum { hash: number; i: number }
type HoverInfo = { x: number; y: number; lines: string[] } | null

// ── Data ──
const declarations: Decl[] = (treeData as any).declarations
const nerves: Nerve[] = (hyperData as any).nerves
const declList = declarations.map(d => d.name)
const uniqueNerves: Nerve[] = (() => {
  const seen = new Set<number>()
  return nerves.filter(n => { if (seen.has(n.hash)) return false; seen.add(n.hash); return true })
})()
const nerveLookup = new Map<number, Nerve>()
for (const n of uniqueNerves) nerveLookup.set(n.hash, n)
function collectTreeHashes(node: TreeNode, set: Set<number>) { set.add(node.hash); node.children.forEach(c => collectTreeHashes(c, set)) }
const declTreeHashes = new Map<string, Set<number>>()
for (const d of declarations) { const s = new Set<number>(); collectTreeHashes(d.value ?? d.type, s); declTreeHashes.set(d.name, s) }

// In-degree lookup
const inDegMap = new Map<number, number>()
for (const n of uniqueNerves) { if (n.ref.length > 1) for (const r of n.ref) inDegMap.set(r, (inDegMap.get(r) || 0) + 1) }

// ── Palette ──
const P = {
  bg: '#0a0b0d', panel: '#111318',
  sep: 'rgba(212,169,116,0.08)', border: 'rgba(212,169,116,0.12)',
  text: '#d4c4a8', accent: '#e8a860', amber: '#d4b996',
  sub: '#8a7e6a', dim: '#4a4036',
  scanline: 'repeating-linear-gradient(0deg,transparent,transparent 2px,rgba(212,169,116,0.02) 2px,rgba(212,169,116,0.02) 3px)',
}

function tagColor(tag: string): string {
  return ({ BVar:'#d4a574', Sort:'#c8a8d4', Const:'#e8c080', Lit:'#d4b096',
    App:'#a8c496', Lam:'#9eb8d0', ForallE:'#b89ed0', LetE:'#c4a890', Decl:'#e89860' })[tag] ?? '#8a7e6a'
}
function nerveTag(r: string): string {
  for (const t of ['BVar','Sort','Const','App','Lam','ForallE','LetE','Decl']) if (r.startsWith(t+'(')) return t
  if (r.startsWith('NatLit(') || r.startsWith('StrLit(')) return 'Lit'
  return 'Other'
}
const nerveTagMap = new Map<number, string>()
for (const n of uniqueNerves) nerveTagMap.set(n.hash, nerveTag(n.record))

function nodeLabel(n: TreeNode): string {
  if (n.tag === 'Const') return n.name || 'C'
  if (n.tag === 'BVar') return `#${n.index ?? '?'}`
  if (n.tag === 'Sort') return '*'
  if (n.tag === 'App') return '@'
  if (n.tag === 'Lam') return '\u03bb'
  if (n.tag === 'ForallE') return '\u2200'
  if (n.tag === 'LetE') return 'let'
  if (n.tag === 'Lit') return 'lit'
  return '?'
}
const NODE_H = 20, NODE_CHAR_W = 6.5, NODE_PAD = 12
function nodeW(label: string): number { return Math.max(NODE_H, label.length * NODE_CHAR_W + NODE_PAD) }
function isPill(label: string): boolean { return nodeW(label) > NODE_H }
function countNodes(n: TreeNode): number { return 1 + n.children.reduce((a, c) => a + countNodes(c), 0) }

function applyHL(nEls: any, eEls: any, active: Set<number>, sel: number | null, ring?: any) {
  nEls
    .attr('r', (d: SimNode) => active.has(d.hash) ? 5 : 2)
    .attr('fill', (d: SimNode) => { const c = tagColor(nerveTagMap.get(d.hash)||''); return active.has(d.hash) ? c : '#181a1f' })
    .attr('stroke', (d: SimNode) => active.has(d.hash) ? tagColor(nerveTagMap.get(d.hash) || '') : '#1e2026')
    .attr('stroke-width', (d: SimNode) => active.has(d.hash) ? 0.5 : 0.2)
    .attr('opacity', (d: SimNode) => active.has(d.hash) ? 0.9 : 0.25)
  if (ring) {
    if (sel !== null) {
      const nd = nEls.data().find((d: SimNode) => d.hash === sel)
      if (nd) ring.attr('cx', nd.x).attr('cy', nd.y).attr('opacity', 0.8)
      else ring.attr('opacity', 0)
    } else ring.attr('opacity', 0)
  }
  eEls
    .attr('stroke', (l: any) => active.has(l.source.hash) && active.has(l.target.hash) ? 'rgba(82,255,153,0.55)' : 'rgba(50,180,100,0.12)')
    .attr('stroke-width', (l: any) => active.has(l.source.hash) && active.has(l.target.hash) ? 1 : 0.5)
}

// ── Fonts & Styles ──
const FM = "'JetBrains Mono','Berkeley Mono','Menlo',monospace"
const FD = "'Space Grotesk','Inter',sans-serif"
const lbl: React.CSSProperties = { fontSize: 10, fontFamily: FM, color: P.dim, letterSpacing: '0.08em', textTransform: 'uppercase' as const, fontVariantNumeric: 'tabular-nums' }
const sec: React.CSSProperties = { fontSize: 11, fontFamily: FM, color: P.dim, letterSpacing: '0.1em', textTransform: 'uppercase' as const, fontWeight: 500 }
const val: React.CSSProperties = { fontSize: 13, fontFamily: FM, color: P.amber, fontWeight: 500, fontVariantNumeric: 'tabular-nums' }

function centerOnHash(hash: number, nodes: SimNode[], svg: any, zoomBehavior: any) {
  const nd = nodes.find(n => n.hash === hash)
  if (!nd || !svg) return
  svg.transition().duration(400).call(zoomBehavior.transform, zoomIdentity.translate(300, 300).scale(1.5).translate(-nd.x!, -nd.y!))
}

function fitHyperView(nodes: SimNode[], svg: any, zoomBehavior: any) {
  if (nodes.length === 0) return
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity
  for (const n of nodes) { x0 = Math.min(x0, n.x!); x1 = Math.max(x1, n.x!); y0 = Math.min(y0, n.y!); y1 = Math.max(y1, n.y!) }
  const pad = 40, w = x1 - x0 + pad * 2, h = y1 - y0 + pad * 2
  const vw = 600, vh = 600, scale = Math.min(vw / w, vh / h) * 0.85, cx = (x0 + x1) / 2, cy = (y0 + y1) / 2
  svg.transition().duration(400).call(zoomBehavior.transform, zoomIdentity.translate(vw / 2, vh / 2).scale(scale).translate(-cx, -cy))
}

const declMath: Record<string, {statement: string; desc: string}> = {
  'Nat':          { statement: 'ℕ : Type',                                    desc: 'the type of natural numbers' },
  'Nat.zero':     { statement: '0 : ℕ',                                      desc: 'zero, the base case' },
  'Nat.succ':     { statement: 'S : ℕ → ℕ',                                  desc: 'successor function' },
  'Nat.rec':      { statement: 'rec : C 0 → (∀ n, C n → C (S n)) → ∀ n, C n', desc: 'induction principle for ℕ' },
  'Nat.add':      { statement: 'n + m := rec m (λ _ r, S r) n',              desc: 'addition by recursion on first arg' },
  'Eq':           { statement: '= : α → α → Prop',                           desc: 'propositional equality' },
  'Eq.refl':      { statement: 'refl : ∀ a, a = a',                          desc: 'reflexivity of equality' },
  'Eq.rec':       { statement: 'rec : C a → a = b → C b',                    desc: 'substitution principle' },
  'Nat.add_zero': { statement: '∀ n, n + 0 = n',                             desc: 'zero is right identity for +' },
  'Nat.add_succ': { statement: '∀ n m, n + S m = S (n + m)',                 desc: 'addition unfolds successor' },
  'zero_add':     { statement: '∀ n, 0 + n = n',                             desc: 'zero is left identity for +' },
  'succ_add':     { statement: '∀ n m, S n + m = S (n + m)',                 desc: 'successor distributes over +' },
  'Eq.symm':      { statement: '∀ a b, a = b → b = a',                       desc: 'symmetry of equality' },
  'Eq.trans':     { statement: '∀ a b c, a = b → b = c → a = c',            desc: 'transitivity of equality' },
  'Nat.add_comm': { statement: '∀ n m, n + m = m + n',                       desc: 'commutativity of addition' },
}

export default function Page() {
  const [decl, setDecl] = useState(declList[declList.length - 1])
  const [selectedHash, setSelectedHash] = useState<number | null>(null)
  const [selHistory, setSelHistory] = useState<number[]>([])
  const [splitPct, setSplitPct] = useState(78)
  const [buildStep, setBuildStep] = useState(0)
  const [isPlaying, setIsPlaying] = useState(true)
  const [hover, setHover] = useState<HoverInfo>(null)
  const treeSvgRef = useRef<SVGSVGElement>(null), treeGRef = useRef<SVGGElement>(null)
  const svgRef = useRef<SVGSVGElement>(null)
  const nodeElsRef = useRef<any>(null), edgeElsRef = useRef<any>(null), ringElRef = useRef<any>(null)
  const hyperZoomRef = useRef<any>(null), hyperSvgSelRef = useRef<any>(null), hyperNodesRef = useRef<SimNode[]>([])
  const treeZoomRef = useRef<any>(null), treeSvgSelRef = useRef<any>(null)
  const setSelRef = useRef(setSelectedHash), selValRef = useRef(selectedHash)
  const setHoverRef = useRef(setHover)
  setSelRef.current = setSelectedHash; selValRef.current = selectedHash; setHoverRef.current = setHover

  // Select with history
  const selectHash = useCallback((h: number | null) => {
    if (h !== null && selectedHash !== null && h !== selectedHash) setSelHistory(prev => [...prev.slice(-20), selectedHash])
    setIsPlaying(false)
    setSelectedHash(h)
  }, [selectedHash])
  const selectHashRef = useRef(selectHash); selectHashRef.current = selectHash

  const goBack = useCallback(() => {
    if (selHistory.length === 0) return
    const prev = selHistory[selHistory.length - 1]
    setSelHistory(h => h.slice(0, -1))
    setSelectedHash(prev)
  }, [selHistory])

  // Reset both panels
  const resetBothPanels = useCallback(() => {
    setSelectedHash(null)
    if (treeZoomRef.current && treeSvgSelRef.current)
      treeSvgSelRef.current.transition().duration(400).call(treeZoomRef.current.transform, zoomIdentity)
    if (hyperZoomRef.current && hyperSvgSelRef.current && hyperNodesRef.current.length)
      fitHyperView(hyperNodesRef.current, hyperSvgSelRef.current, hyperZoomRef.current)
  }, [])

  // ── Force graph ──
  useEffect(() => {
    if (!svgRef.current) return
    const svg = select(svgRef.current); svg.selectAll('*').remove()
    const g = svg.append('g')
    const zb = zoom<SVGSVGElement, unknown>().scaleExtent([0.1, 20]).on('zoom', e => g.attr('transform', e.transform.toString()))
    svg.call(zb as any)
    svg.on('click', (e: any) => { if (e.target === svgRef.current) resetBothPanels() })
    hyperZoomRef.current = zb; hyperSvgSelRef.current = svg

    const hToI = new Map<number, number>()
    const nodes: SimNode[] = uniqueNerves.map((n, i) => { hToI.set(n.hash, i); return { hash: n.hash, i, x: 300+(Math.random()-0.5)*100, y: 300+(Math.random()-0.5)*100 } })
    const links: {source:number;target:number}[] = []
    for (const n of uniqueNerves) { if (n.ref.length<=1) continue; const si=hToI.get(n.hash)!; for (const r of n.ref) { const ti=hToI.get(r); if(ti!==undefined&&ti!==si) links.push({source:si,target:ti}) } }

    const eEls = g.append('g').selectAll('line').data(links).enter().append('line').attr('stroke','rgba(50,180,100,0.12)').attr('stroke-width',0.5)
    const nEls = g.append('g').selectAll('circle').data(nodes).enter().append('circle')
      .attr('r',2).attr('fill','#181a1f').attr('stroke','#1e2026').attr('stroke-width',0.3).attr('opacity',0.25)
      .style('cursor','pointer').style('transition','r 120ms ease-out, stroke-width 120ms ease-out')
      .on('click',(_:any,d:SimNode)=>{ selectHashRef.current(d.hash) })
      .on('mouseover',function(_:any,d:SimNode){
        select(this).attr('stroke',P.accent).attr('stroke-width',1.5).attr('r',
          (select(this).attr('opacity') as any) > 0.5 ? 7 : 3)
        const nv = nerveLookup.get(d.hash); const tg = nerveTagMap.get(d.hash)||'?'
        setHoverRef.current({x:0,y:0, lines:[
          `Tag: ${tg}`, `Hash: ${String(d.hash).slice(0,12)}...`,
          `Ref: ${nv?.ref.length??0}`, `In-degree: ${inDegMap.get(d.hash)||0}`,
          `Origin: ${nv?.decl??'?'}, ${nv?.phase??'?'}, step ${nv?.step??'?'}`
        ]})
      })
      .on('mouseout',function(this:SVGCircleElement,_:any,d:SimNode){
        // Restore to applyHL state
        const isActive = (select(this).attr('opacity') as any) > 0.5
        select(this).attr('stroke', isActive ? tagColor(nerveTagMap.get(d.hash)||'') : '#1e2026')
          .attr('stroke-width', isActive ? 0.5 : 0.2)
          .attr('r', isActive ? 5 : 2)
        setHoverRef.current(null)
      })
      .on('mousemove',(e:any)=>{setHoverRef.current(h=>h?{...h,x:e.clientX,y:e.clientY}:null)})

    const ring = g.append('circle').attr('r',9).attr('fill','none').attr('stroke',P.accent).attr('stroke-width',0.8).attr('stroke-dasharray','3 2').attr('opacity',0).style('pointer-events','none')
    let ro = 0
    nodeElsRef.current=nEls; edgeElsRef.current=eEls; ringElRef.current=ring

    const sim = forceSimulation(nodes).force('link',forceLink(links).distance(18).strength(0.5)).force('charge',forceManyBody().strength(-40)).force('center',forceCenter(300,300).strength(0.05)).force('collide',forceCollide(6)).alpha(1).alphaDecay(0.02).velocityDecay(0.4).stop()
    for(let i=0;i<300;i++)sim.tick()
    hyperNodesRef.current = nodes
    fitHyperView(nodes, svg, zb)
    sim.alpha(0.1).restart().on('tick',()=>{
      eEls.attr('x1',(d:any)=>d.source.x).attr('y1',(d:any)=>d.source.y).attr('x2',(d:any)=>d.target.x).attr('y2',(d:any)=>d.target.y)
      nEls.attr('cx',(d:any)=>d.x).attr('cy',(d:any)=>d.y)
      ro=(ro+0.15)%10; ring.attr('stroke-dashoffset',ro)
      const sh=selValRef.current; if(sh!==null){const nd=nodes.find(n=>n.hash===sh); if(nd)ring.attr('cx',nd.x!).attr('cy',nd.y!)}
    })

    const db = drag<SVGCircleElement,SimNode>()
      .on('start',(ev,d)=>{if(!ev.active)sim.alphaTarget(0.3).restart();d.fx=d.x;d.fy=d.y})
      .on('drag',(ev,d)=>{d.fx=ev.x;d.fy=ev.y})
      .on('end',(ev,d)=>{if(!ev.active)sim.alphaTarget(0);d.fx=null;d.fy=null})
    nEls.call(db as any)
    applyHL(nEls,eEls,new Set(),null,ring)
    return ()=>{sim.stop()}
  },[])

  // Decl change
  useEffect(() => {
    if (hyperZoomRef.current && hyperSvgSelRef.current && hyperNodesRef.current.length)
      fitHyperView(hyperNodesRef.current, hyperSvgSelRef.current, hyperZoomRef.current)
    setBuildStep(0); setIsPlaying(false); setSelectedHash(null); setSelHistory([]); setHover(null)
    const t = setTimeout(() => setIsPlaying(true), 150)
    return () => clearTimeout(t)
  }, [decl])

  // Keyboard: arrow keys switch decl
  useEffect(() => {
    const handler = (e: KeyboardEvent) => {
      if (e.target instanceof HTMLInputElement) return
      const idx = declList.indexOf(decl)
      if (e.key === 'ArrowLeft' && idx > 0) setDecl(declList[idx - 1])
      if (e.key === 'ArrowRight' && idx < declList.length - 1) setDecl(declList[idx + 1])
    }
    window.addEventListener('keydown', handler)
    return () => window.removeEventListener('keydown', handler)
  }, [decl])

  // ── Tree ──
  const cd = declarations.find(d=>d.name===decl)!
  const tree = cd.value ?? cd.type
  const nc = useMemo(()=>countNodes(tree),[tree])
  useEffect(() => {
    if (!isPlaying) return
    const totalMs = Math.max(400, Math.min(3000, nc * 30))
    const iv = setInterval(() => {
      setBuildStep(s => { if (s >= nc) { setIsPlaying(false); return nc }; return s + 1 })
    }, Math.max(50, totalMs / nc))
    return () => clearInterval(iv)
  }, [isPlaying, nc])

  const {treeRoot,treeVB} = useMemo(()=>{
    const root = hierarchy(tree,d=>d.children)
    const baseU = 24
    d3tree<TreeNode>().nodeSize([baseU, 50]).separation((a, b) => {
      const wA = nodeW(nodeLabel(a.data)), wB = nodeW(nodeLabel(b.data))
      const needed = (wA / 2 + wB / 2 + 8) / baseU
      return a.parent === b.parent ? Math.max(1, needed) : Math.max(1.5, needed)
    })(root)
    const pad = 20; let x0=Infinity,x1=-Infinity,y0=Infinity,y1=-Infinity
    root.each(n=>{
      const hw = nodeW(nodeLabel(n.data)) / 2
      x0=Math.min(x0,n.x!-hw);x1=Math.max(x1,n.x!+hw);y0=Math.min(y0,n.y!-NODE_H/2);y1=Math.max(y1,n.y!+NODE_H/2)
    })
    return {treeRoot:root, treeVB:`${x0-pad} ${y0-pad} ${x1-x0+pad*2} ${y1-y0+pad*2}`}
  },[tree])

  useEffect(()=>{
    if(!treeSvgRef.current||!treeGRef.current)return
    const g=treeGRef.current
    g.setAttribute('transform', '') // reset to identity
    const zb = zoom<SVGSVGElement,unknown>().scaleExtent([0.3,10]).on('zoom',e=>g.setAttribute('transform',e.transform.toString()))
    const svgSel = select(treeSvgRef.current); svgSel.call(zb as any)
    svgSel.call(zb.transform, zoomIdentity) // reset zoom state
    treeZoomRef.current = zb; treeSvgSelRef.current = svgSel
  },[tree])

  const visH = useMemo(()=>{const s=new Set<number>(); function c(n:TreeNode){if(n.step<=buildStep)s.add(n.hash);n.children.forEach(c)};c(tree);return s},[tree,buildStep])
  const nrv = visH.size
  useEffect(()=>{if(nodeElsRef.current&&edgeElsRef.current)applyHL(nodeElsRef.current,edgeElsRef.current,visH,selectedHash,ringElRef.current)},[visH])
  useEffect(()=>{if(nodeElsRef.current&&edgeElsRef.current)applyHL(nodeElsRef.current,edgeElsRef.current,visH,selectedHash,ringElRef.current)},[selectedHash])

  // Center on selected
  useEffect(() => {
    if (selectedHash === null) return
    if (hyperZoomRef.current && hyperSvgSelRef.current && hyperNodesRef.current.length)
      centerOnHash(selectedHash, hyperNodesRef.current, hyperSvgSelRef.current, hyperZoomRef.current)
    if (treeZoomRef.current && treeSvgSelRef.current && treeRoot) {
      const match = treeRoot.descendants().find(d => d.data.hash === selectedHash)
      if (match) {
        const vb = (treeSvgSelRef.current.node() as SVGSVGElement).viewBox.baseVal
        treeSvgSelRef.current.transition().duration(400).call(
          treeZoomRef.current.transform, zoomIdentity.translate(vb.width/2, vb.height/2).scale(2).translate(-match.x!, -match.y!)
        )
      }
    }
  }, [selectedHash])

  // ── Detail ──
  const selNerve = selectedHash ? nerveLookup.get(selectedHash)||null : null
  const selTag = selectedHash ? (nerveTagMap.get(selectedHash) || (selNerve ? nerveTag(selNerve.record) : '?')) : null
  const selTree = useMemo(()=>{
    if(!selectedHash)return {count:0,decls:[] as string[]}
    let count=0; const ds=new Set<string>()
    for(const d of declarations){function s(n:TreeNode){if(n.hash===selectedHash){count++;ds.add(d.name)};n.children.forEach(s)};s(d.type);if(d.value)s(d.value)}
    return {count,decls:[...ds]}
  },[selectedHash])
  const inDeg = selectedHash ? (inDegMap.get(selectedHash) || 0) : 0
  const sl = Math.min(buildStep,nc)

  // ── Render ──
  return (
    <div style={{fontFamily:FM,background:P.bg,color:P.sub,height:'100vh',display:'flex',flexDirection:'column',fontSize:12}}>
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500;700&family=Space+Grotesk:wght@400;500;600&display=swap');
        @keyframes dash{to{stroke-dashoffset:10}}
        ::selection{background:rgba(212,169,116,0.3);color:#d4c4a8}
        input[type=range]{-webkit-appearance:none;appearance:none;background:#1a1d22;height:4px;border-radius:0;outline:none}
        input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:3px;height:14px;background:#e8a860;border:none;border-radius:0;cursor:pointer}
        input[type=range]::-moz-range-thumb{width:3px;height:14px;background:#e8a860;border:none;border-radius:0;cursor:pointer}
        *{box-sizing:border-box}
        button:focus-visible,input:focus-visible{outline:1px solid #e8a860;outline-offset:2px}
        .split-grid{display:grid;grid-template-columns:1fr 1fr}
        .detail-grid{display:grid;grid-template-columns:1fr 1fr;gap:24px}
        @media(max-width:800px){
          .split-grid{grid-template-columns:1fr!important;grid-template-rows:1fr 1fr}
          .detail-grid{grid-template-columns:1fr!important}
          .mobile-hide{display:none!important}
          .header-title{font-size:13px!important}
          .tab-bar{overflow-x:auto!important;justify-content:flex-start!important;gap:0!important;-webkit-overflow-scrolling:touch}
          .tab-bar button{font-size:9px!important;padding:6px 4px!important;flex:0 0 auto!important}
        }
      `}</style>

      {/* Header */}
      <div style={{borderBottom:`1px solid ${P.sep}`,padding:'14px 16px',display:'flex',alignItems:'center',justifyContent:'space-between',flexShrink:0,backgroundImage:P.scanline}}>
        <div style={{display:'flex',alignItems:'center',gap:12}}>
          <a href="https://qedinfra.zulipchat.com" target="_blank" rel="noopener noreferrer"
            style={{color:P.sub,transition:'color 120ms ease',display:'flex',alignItems:'center'}}
            onMouseEnter={e=>(e.currentTarget.style.color=P.accent)} onMouseLeave={e=>(e.currentTarget.style.color=P.sub)}>
            <svg width="20" height="20" viewBox="0 0 24 24" fill="currentColor">
              <path d="M4.5 2C3.12 2 2 3.12 2 4.5v4.03l7.5 3.97L2 16.47V19.5C2 20.88 3.12 22 4.5 22h15c1.38 0 2.5-1.12 2.5-2.5v-4.03l-7.5-3.97L22 7.53V4.5C22 3.12 20.88 2 19.5 2h-15zM4.5 4h15c.28 0 .5.22.5.5v1.72l-8 4.24-8-4.24V4.5c0-.28.22-.5.5-.5zm-1 13.28l8-4.24 8 4.24v1.22c0 .28-.22.5-.5.5h-15a.5.5 0 01-.5-.5v-1.22z"/>
            </svg>
          </a>
          <a href="https://github.com/MathNetwork/cic-kernal" target="_blank" rel="noopener noreferrer"
            style={{color:P.sub,transition:'color 120ms ease',display:'flex',alignItems:'center'}}
            onMouseEnter={e=>(e.currentTarget.style.color=P.accent)} onMouseLeave={e=>(e.currentTarget.style.color=P.sub)}>
            <svg width="20" height="20" viewBox="0 0 16 16" fill="currentColor">
              <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0016 8c0-4.42-3.58-8-8-8z"/>
            </svg>
          </a>
        </div>
        <span className="header-title" style={{fontFamily:FD,color:P.text,fontSize:18,fontWeight:500,letterSpacing:'-0.01em'}}>CIC Type-Checking as Growing a Content-Addressed Hypergraph</span>
        <div style={{width:52}}/>
      </div>

      {/* Tabs */}
      <div className="tab-bar" style={{borderBottom:`1px solid ${P.sep}`,display:'flex',justifyContent:'space-between',padding:'0 8px',flexShrink:0}}>
        {declList.map((d,i)=>{
          const selIdx = declList.indexOf(decl)
          const col = i === selIdx ? P.text : i < selIdx ? '#b89870' : '#6a6050'
          return (
            <button key={d} onClick={()=>setDecl(d)} style={{
              padding:'8px 4px',fontSize:11,whiteSpace:'nowrap',cursor:'pointer',fontFamily:FM,
              border:'none',flex:'1 1 0',textAlign:'center',minWidth:0,
              background:'transparent',color:col,
              letterSpacing:'0.02em',transition:'color 120ms ease',
            }}>{d===decl?`[ ${d} ]`:d}</button>
          )
        })}
      </div>

      {/* Description bar */}
      <div className="mobile-hide" style={{borderBottom:`1px solid ${P.sep}`,padding:'8px 16px',backgroundImage:P.scanline,flexShrink:0,display:'flex',justifyContent:'space-between',alignItems:'baseline'}}>
        <div>
          <span style={{color:P.amber,fontSize:14,fontFamily:FD,fontWeight:500}}>{declMath[decl]?.statement || decl}</span>
          <span style={{color:P.dim,fontSize:11,marginLeft:12}}>{declMath[decl]?.desc || cd.kind}</span>
        </div>
        <span style={{...lbl,fontSize:9}}>{cd.kind}</span>
      </div>

      {/* Main */}
      <div style={{flex:1,display:'flex',flexDirection:'column',overflow:'hidden'}}>
        {/* Section headers — full width grid matching panel split */}
        <div className="split-grid" style={{flexShrink:0,borderBottom:`1px solid ${P.sep}`}}>
          <div style={{padding:'6px 8px',borderRight:`1px solid ${P.sep}`,...sec}}>
            tree · <span style={{color:P.sub}}>{decl}</span> · {cd.kind}
          </div>
          <div style={{padding:'6px 8px',...sec,display:'flex',gap:4}}>
            <span>hypergraph</span>
            <span style={{color:P.dim}}>|</span>
            <span>total [{uniqueNerves.length}]</span>
            <span style={{color:P.dim}}>|</span>
            <span>active <span style={val}>[{nrv}]</span></span>
            <span style={{color:P.dim}}>|</span>
            <span>{nc}→{nrv}</span>
          </div>
        </div>
        <div className="split-grid" style={{height:`${splitPct}%`,overflow:'hidden'}}>

          {/* Left: Tree */}
          <div style={{borderRight:`1px solid ${P.sep}`,overflow:'hidden',display:'flex',flexDirection:'column',position:'relative'}}>
            <svg style={{position:'absolute',top:0,left:0,width:'100%',height:'100%',pointerEvents:'none',zIndex:1}}>
              {[[4,4,'h'],[4,4,'v']].map(([x,y,d],i)=>
                <line key={`tl${i}`} x1={Number(x)} y1={Number(y)} x2={d==='h'?12:4} y2={d==='v'?12:4} stroke={P.sub} strokeWidth={0.4} opacity={0.4}/>
              )}
            </svg>
            <svg ref={treeSvgRef} viewBox={treeVB} preserveAspectRatio="xMidYMid meet" style={{flex:1,width:'100%',background:P.panel,backgroundImage:P.scanline}}
              onClick={e => { if (e.target === treeSvgRef.current) resetBothPanels() }}>
              <g ref={treeGRef}>
                {treeRoot.links().map((lk,i)=>{
                  const v=lk.source.data.step<=buildStep&&lk.target.data.step<=buildStep
                  return <line key={i} x1={lk.source.x} y1={lk.source.y} x2={lk.target.x} y2={lk.target.y} stroke={v?'rgba(67,220,130,0.25)':'transparent'} strokeWidth={0.6}/>
                })}
                {treeRoot.descendants().map((d,i)=>{
                  const v=d.data.step<=buildStep, col=tagColor(d.data.tag), lab=nodeLabel(d.data), w=nodeW(lab), pill=isPill(lab), isSel=selectedHash===d.data.hash
                  return (
                    <g key={i} opacity={v?1:0.05} style={{cursor:v?'pointer':'default',transition:'opacity 150ms ease'}}
                      onClick={(e)=>{e.stopPropagation();if(v)selectHash(d.data.hash)}}
                      onMouseEnter={(e)=>{if(!v)return;setHover({x:e.clientX,y:e.clientY,lines:[
                        `Tag: ${d.data.tag}`,`Hash: ${String(d.data.hash).slice(0,12)}...`,
                        `Step: ${d.data.step}`,`Decl: ${decl}`
                      ]})}}
                      onMouseMove={(e)=>setHover(h=>h?{...h,x:e.clientX,y:e.clientY}:null)}
                      onMouseLeave={()=>setHover(null)}>
                      {isSel && (pill
                        ? <rect x={d.x!-w/2-3} y={d.y!-NODE_H/2-3} width={w+6} height={NODE_H+6} rx={NODE_H/2+3} fill="none" stroke={P.accent} strokeWidth={0.8} strokeDasharray="3 2" style={{animation:'dash 1.5s linear infinite'}}/>
                        : <circle cx={d.x} cy={d.y} r={NODE_H/2+4} fill="none" stroke={P.accent} strokeWidth={0.8} strokeDasharray="3 2" style={{animation:'dash 1.5s linear infinite'}}/>
                      )}
                      {pill
                        ? <rect x={d.x!-w/2} y={d.y!-NODE_H/2} width={w} height={NODE_H} rx={NODE_H/2} fill={col} fillOpacity={0.15} stroke={col} strokeWidth={isSel?1.5:0.8} opacity={0.85}/>
                        : <circle cx={d.x} cy={d.y} r={NODE_H/2} fill={col} fillOpacity={0.15} stroke={col} strokeWidth={isSel?1.5:0.8} opacity={0.85}/>
                      }
                      <text x={d.x} y={d.y} textAnchor="middle" dominantBaseline="central" fill={col} fontSize={10} fontWeight={500} fontFamily={FM} pointerEvents="none">{lab}</text>
                    </g>
                  )
                })}
              </g>
            </svg>
          </div>

          {/* Right: Hypergraph */}
          <div style={{overflow:'hidden',display:'flex',flexDirection:'column'}}>
            <svg ref={svgRef} viewBox="0 0 600 600" style={{flex:1,width:'100%',background:P.panel,backgroundImage:P.scanline}}/>
          </div>
        </div>

        {/* Full-width slider */}
        <div style={{padding:'4px 16px 8px',flexShrink:0,display:'flex',alignItems:'center',gap:12,borderBottom:`1px solid ${P.sep}`}}>
          <div style={{...lbl,color:P.dim,fontSize:9,whiteSpace:'nowrap'}}>post-order build</div>
          <div style={{flex:1,position:'relative'}}>
            <svg style={{position:'absolute',top:-6,left:0,width:'100%',height:6,pointerEvents:'none'}}>
              {Array.from({length:11},(_,i)=>{
                const pct=i*10; const isMajor=pct%50===0
                return <line key={i} x1={`${pct}%`} y1={isMajor?1:3} x2={`${pct}%`} y2={6}
                  stroke={isMajor?'rgba(212,169,116,0.5)':'rgba(212,169,116,0.3)'} strokeWidth={1}/>
              })}
            </svg>
            <input type="range" min={1} max={nc} value={sl} onChange={e=>{setIsPlaying(false);setBuildStep(Number(e.target.value))}} style={{width:'100%'}}/>
          </div>
          <div style={{display:'flex',alignItems:'center',gap:4}}>
            <button onClick={()=>{setBuildStep(0);setIsPlaying(true)}} style={{
              background:'none',border:`1px solid ${P.border}`,color:P.sub,cursor:'pointer',fontFamily:FM,fontSize:14,padding:'4px 10px',lineHeight:1,
            }}>⟳</button>
            <button onClick={()=>{setIsPlaying(false);setBuildStep(s=>Math.max(1,s-1))}} style={{
              background:'none',border:`1px solid ${P.border}`,color:P.sub,cursor:'pointer',fontFamily:FM,fontSize:14,padding:'4px 10px',lineHeight:1,
            }}>◀</button>
            <button onClick={()=>{setIsPlaying(false);setBuildStep(s=>Math.min(nc,s+1))}} style={{
              background:'none',border:`1px solid ${P.border}`,color:P.sub,cursor:'pointer',fontFamily:FM,fontSize:14,padding:'4px 10px',lineHeight:1,
            }}>▶</button>
          </div>
          <div style={{minWidth:90,textAlign:'right'}}>
            <span style={{...lbl,color:P.dim,fontSize:9}}>step </span>
            <span style={{fontFamily:FD,fontSize:18,fontWeight:500,color:P.accent}}>{sl}</span>
            <span style={{fontSize:11,color:P.sub,marginLeft:2}}> of {nc}</span>
          </div>
        </div>

        {/* Detail */}
        <div style={{flex:1,overflow:'auto',minHeight:0,padding:'10px 16px',fontSize:13,background:P.panel,backgroundImage:P.scanline}}>
          {selectedHash ? (
            <div className="detail-grid">
              <div>
                <div style={{display:'flex',justifyContent:'space-between',marginBottom:6}}>
                  <span style={sec}>tree occurrences{selTag ? ` · ${selTag}` : ''}</span>
                  <div style={{display:'flex',gap:6}}>
                    {selHistory.length > 0 && <button onClick={goBack} style={{background:'none',border:'none',color:P.accent,cursor:'pointer',fontSize:11,fontFamily:FM}}>← back</button>}
                    <button onClick={()=>setSelectedHash(null)} style={{background:'none',border:'none',color:P.dim,cursor:'pointer',fontSize:11}}>×</button>
                  </div>
                </div>
                <div style={{marginBottom:3}}><span style={lbl}>decls </span><span style={{color:P.text}}>{selTree.decls.join(', ')}</span></div>
                <div><span style={lbl}>occurrences </span><span style={{color:P.text,fontWeight:500}}>{selTree.count}</span></div>
              </div>
              <div>
                <div style={{...sec,marginBottom:6}}>nerve <span style={{...val,fontSize:13}}>{selectedHash}</span></div>
                {selNerve ? (<>
                  <div style={{wordBreak:'break-all',marginBottom:3}}><span style={lbl}>record </span><span style={{color:P.text}}>{selNerve.record}</span></div>
                  <div style={{marginBottom:3}}><span style={lbl}>ref</span>
                    {selNerve.ref.map((r,i) => {
                      const rn = nerveLookup.get(r)
                      const tag = rn ? rn.record.slice(0, rn.record.indexOf('(')) : '?'
                      return (
                        <div key={i} style={{marginLeft:16,marginTop:2}}>
                          <span onClick={()=>selectHash(r)} style={{color:P.accent,cursor:'pointer',textDecoration:'underline',textDecorationColor:'rgba(212,169,116,0.3)',textUnderlineOffset:2}}>{r}</span>
                          <span style={{color:P.dim,marginLeft:6,fontSize:11}}>{tag}{rn ? `(${rn.record.slice(rn.record.indexOf('(')+1, Math.min(rn.record.indexOf('(')+25, rn.record.length))}` : ''}</span>
                        </div>
                      )
                    })}
                  </div>
                  <div style={{marginBottom:3}}><span style={lbl}>origin </span><span style={{color:P.accent}}>{selNerve.decl}</span> · {selNerve.phase} · step {selNerve.step}</div>
                  <div><span style={lbl}>in-degree </span><span style={{color:P.text,fontWeight:500}}>{inDeg}</span><span style={{color:P.dim,fontSize:11}}> / {uniqueNerves.length}</span></div>
                </>) : <span style={sec}>no matching nerve</span>}
              </div>
            </div>
          ) : (
            <div>
              <div style={{...lbl,height:24,display:'flex',alignItems:'center'}}><span style={{color:P.accent,marginRight:6}}>▸</span>select a node to inspect</div>
              <div style={{color:'#a8956a',fontSize:11,marginTop:4,lineHeight:1.5}}>
                Left: expression tree of each CIC declaration.<br/>
                Right: content-addressed hypergraph where identical sub-expressions share a single nerve.
              </div>
            </div>
          )}
        </div>
      </div>

      {/* Tooltip */}
      {hover && (
        <div style={{
          position:'fixed',left:Math.min(hover.x+12,window.innerWidth-200),top:Math.min(hover.y+12,window.innerHeight-100),
          background:'rgba(17,19,24,0.95)',border:`1px solid ${P.border}`,
          padding:'6px 10px',fontSize:10,lineHeight:1.4,fontFamily:FM,color:P.text,
          pointerEvents:'none',zIndex:100,maxWidth:200,
        }}>
          {hover.lines.map((l,i)=><div key={i}>{l}</div>)}
        </div>
      )}
    </div>
  )
}
