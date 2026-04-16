import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Filter.Basic

namespace Astrolabe

variable {Hash : Type} [DecidableEq Hash] [Inhabited Hash]

structure AstroNerve (Hash : Type) where
  id : Hash
  ref : List Hash
  record : String
  deriving DecidableEq, Inhabited, Repr

def AstroNerve.width (e : AstroNerve Hash) : Nat := e.ref.length - 1

def AstroNerve.isAtom (e : AstroNerve Hash) : Prop := e.width = 0

structure AstroNet (Hash : Type) [DecidableEq Hash] where
  entries : Finset (AstroNerve Hash)
  hash : String → Hash
  consistent : ∀ e, e ∈ entries → e.id = hash e.record
  selfRef : ∀ e, e ∈ entries → e.width = 0 → e.ref = [e.id]
  injectivity : ∀ e₁, e₁ ∈ entries → ∀ e₂, e₂ ∈ entries → e₁.id = e₂.id → e₁ = e₂
  closure : ∀ e, e ∈ entries → ∀ r, r ∈ e.ref → ∃ e' ∈ entries, e'.id = r
  noSelfRef : ∀ e, e ∈ entries → e.width > 0 → e.id ∉ e.ref

omit [Inhabited Hash] in
theorem AstroNet.nonEmpty (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) : e.ref.length ≥ 1 := by
  by_cases hdeg : e.width = 0
  · rw [S.selfRef e he hdeg]; simp
  · unfold AstroNerve.width at hdeg
    omega

def F1 (S : AstroNet Hash) : Finset (AstroNerve Hash) :=
  S.entries.filter (fun e => decide (e.width ≤ 1))

/-! ## Examples -/

section Examples

/-- An atom: self-referencing, degree 0. -/
def exAtom : AstroNerve String := ⟨"a", ["a"], "a"⟩

/-- A binary edge: degree 1. -/
def exEdge : AstroNerve String := ⟨"e1", ["a", "b"], "e1"⟩

/-- A ternary entry: degree 2. -/
def exTernary : AstroNerve String := ⟨"t1", ["a", "b", "c"], "t1"⟩

#eval exAtom.width    -- 0
#eval exEdge.width    -- 1
#eval exTernary.width -- 2

example : exAtom.width = 0 := rfl
example : exEdge.width = 1 := rfl
example : exAtom.isAtom := rfl

end Examples

def AstroNet.ids (S : AstroNet Hash) : Finset Hash :=
  S.entries.image (fun e => e.id)

/-! ## Stage filtration

Given a well-formed network `S`, define `F₀ ⊆ F₁ ⊆ ⋯ ⊆ S` inductively:
- `F₀ = {e ∈ S | degree(e) = 0}` (atoms)
- `Fₙ₊₁ = {e ∈ S | ∀ r ∈ ref(e), r is the id of some nerve in Fₙ}`

The **stage** of a nerve `e` is `min {n | e ∈ Fₙ}`.
Nerves involved in reference cycles have no finite stage.
-/

def depthFilt (S : AstroNet Hash) : ℕ → Finset (AstroNerve Hash)
  | 0 => S.entries.filter (fun e => decide (e.width = 0))
  | n + 1 => S.entries.filter (fun e =>
      e.ref.all (fun r => r ∈ (depthFilt S n).image (fun e' => e'.id)))

def depthFilt.ids (S : AstroNet Hash) (n : ℕ) : Finset Hash :=
  (depthFilt S n).image (fun e => e.id)

/-! ## Paths and cycles -/

/-- A path in an AstroNet: a sequence of hashes where each consecutive pair
    follows a reference edge, and every node belongs to some entry. -/
structure AstroPath (S : AstroNet Hash) where
  nodes : List Hash
  nonempty : nodes.length ≥ 2
  valid : ∀ i, i + 1 < nodes.length →
    ∃ e ∈ S.entries, e.id = nodes[i]! ∧ nodes[i+1]! ∈ e.ref
  inStore : ∀ h, h ∈ nodes → ∃ e ∈ S.entries, e.id = h

/-- A path is a cycle if it starts and ends at the same node,
    and passes through at least one distinct node. -/
def AstroPath.isCycle {S : AstroNet Hash} (p : AstroPath S) : Prop :=
  p.nodes.head? = p.nodes.getLast? ∧
  ∃ h, h ∈ p.nodes ∧ h ≠ p.nodes.head?.get!

/-- An entry participates in a cycle if its id appears on some cyclic path. -/
def AstroNet.inCycle (S : AstroNet Hash) (e : AstroNerve Hash) : Prop :=
  ∃ p : AstroPath S, p.isCycle ∧ e.id ∈ p.nodes

omit [Inhabited Hash] in
theorem depthFilt_sub_entries (S : AstroNet Hash) (n : ℕ) :
    depthFilt S n ⊆ S.entries := by
  cases n with
  | zero => exact Finset.filter_subset _ _
  | succ n => exact Finset.filter_subset _ _

omit [Inhabited Hash] in
theorem depthFilt_mono (S : AstroNet Hash) (n : ℕ) :
    depthFilt S n ⊆ depthFilt S (n + 1) := by
  induction n with
  | zero =>
    intro e he
    simp only [depthFilt, Finset.mem_filter] at he ⊢
    refine ⟨he.1, ?_⟩
    simp only [decide_eq_true_eq] at he
    have href := S.selfRef e he.1 he.2
    rw [href]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    simp only [Finset.mem_image, decide_eq_true_eq]
    exact ⟨e, Finset.mem_filter.mpr ⟨he.1, by simp [he.2]⟩, rfl⟩
  | succ n ih =>
    intro e he
    have he_ent := depthFilt_sub_entries S (n + 1) he
    show e ∈ depthFilt S (n + 1 + 1)
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl, depthFilt, Finset.mem_filter]
    refine ⟨he_ent, ?_⟩
    rw [depthFilt, Finset.mem_filter] at he
    rw [List.all_eq_true] at he ⊢
    intro r hr
    have hr_in := he.2 r hr
    rw [decide_eq_true_eq] at hr_in ⊢
    rw [Finset.mem_image] at hr_in ⊢
    obtain ⟨e', he', rfl⟩ := hr_in
    exact ⟨e', ih he', rfl⟩

omit [Inhabited Hash] in
theorem depthFilt_mono_le (S : AstroNet Hash) {a b : ℕ} (hab : a ≤ b) :
    depthFilt S a ⊆ depthFilt S b := by
  induction hab with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact Finset.Subset.trans ih (depthFilt_mono S _)

omit [Inhabited Hash] in
theorem depthFilt_stabilizes (S : AstroNet Hash) :
    ∃ N, ∀ n ≥ N, depthFilt S n = depthFilt S N := by
  have hmono : Monotone (fun n => (depthFilt S n).card) :=
    fun _ _ hab => Finset.card_le_card (depthFilt_mono_le S hab)
  have hbdd : ∀ n, (fun n => (depthFilt S n).card) n ≤ S.entries.card :=
    fun n => Finset.card_le_card (depthFilt_sub_entries S n)
  obtain ⟨b, N, hN⟩ := converges_of_monotone_of_bounded hmono hbdd
  exact ⟨N, fun n hn => (Finset.eq_of_subset_of_card_le
    (depthFilt_mono_le S (le_of_eq rfl |>.trans hn))
    (by rw [hN n hn, hN N (le_refl N)])).symm⟩

-- Helper: if e ∈ depthFilt S (n+1), then all refs of e are ids of entries in depthFilt S n
omit [Inhabited Hash] in
theorem depthFilt_succ_refs (S : AstroNet Hash) (e : AstroNerve Hash) (n : ℕ)
    (he : e ∈ depthFilt S (n + 1)) :
    ∀ r ∈ e.ref, ∃ e' ∈ depthFilt S n, e'.id = r := by
  intro r hr
  simp only [depthFilt, Finset.mem_filter] at he
  have hall := he.2
  rw [List.all_eq_true] at hall
  have := hall r hr
  rw [decide_eq_true_eq, Finset.mem_image] at this
  obtain ⟨e', he', rfl⟩ := this
  exact ⟨e', he', rfl⟩

-- Helper: entries in stage 0 have degree 0
omit [Inhabited Hash] in
theorem depthFilt_zero_degree (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ depthFilt S 0) : e.width = 0 := by
  simp only [depthFilt, Finset.mem_filter, decide_eq_true_eq] at he
  exact he.2

-- Helper: if e ∈ S.entries and e ∉ depthFilt S (n+1), then some ref of e
-- is not the id of any entry in depthFilt S n
omit [Inhabited Hash] in
theorem not_depthFilt_succ_exists_ref (S : AstroNet Hash) (e : AstroNerve Hash) (n : ℕ)
    (he : e ∈ S.entries) (hne : e ∉ depthFilt S (n + 1)) :
    ∃ r ∈ e.ref, ∀ e' ∈ depthFilt S n, e'.id ≠ r := by
  by_contra h
  push Not at h
  apply hne
  simp only [depthFilt, Finset.mem_filter]
  refine ⟨he, ?_⟩
  rw [List.all_eq_true]
  intro r hr
  rw [decide_eq_true_eq, Finset.mem_image]
  obtain ⟨e', he', hid⟩ := h r hr
  exact ⟨e', he', hid⟩

-- Helper: if e ∈ S.entries and e ∉ depthFilt S n for all n, then
-- e has a ref r whose corresponding entry is also not in any depthFilt
omit [Inhabited Hash] in
theorem not_in_any_stage_has_unstaged_ref (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) :
    ∃ r ∈ e.ref, ∃ e' ∈ S.entries, e'.id = r ∧ ∀ n, e' ∉ depthFilt S n := by
  -- e ∉ depthFilt S (n+1) for all n, so for each n, some ref is not in stage n's image
  -- We need ONE ref that works for ALL n
  -- Key: by depthFilt_stabilizes, ∃ N, ∀ n ≥ N, depthFilt S n = depthFilt S N
  -- So e ∉ depthFilt S (N+1), meaning some ref r is not in (depthFilt S N).image id
  -- By monotonicity, r is not in (depthFilt S m).image id for any m ≤ N
  -- And for m > N, depthFilt S m = depthFilt S N, so r is not in those either
  obtain ⟨N, hN⟩ := depthFilt_stabilizes S
  have h1 := not_depthFilt_succ_exists_ref S e N he (hne (N + 1))
  obtain ⟨r, hr, hr_not⟩ := h1
  obtain ⟨e', he', hid⟩ := S.closure e he r hr
  refine ⟨r, hr, e', he', hid, ?_⟩
  intro m
  by_contra habs
  have : e' ∈ depthFilt S N := by
    by_cases hm : m ≤ N
    · exact depthFilt_mono_le S hm habs
    · rw [← hN m (by omega)]; exact habs
  exact absurd hid (hr_not e' this)

-- Helper: if e ∈ depthFilt S n, then e is not in any cycle
-- Proved by strong induction on n.
-- Helper: on a cycle, every node has a successor on the cycle via a ref edge
-- Moreover, the successor can be chosen to be a *different* node from the current one
-- (since cycles have at least one distinct node and wrap around)
-- Helper: for any h ∈ p.nodes, there exists i with i+1 < p.nodes.length and p.nodes[i] = h
-- (on a cycle, the last element equals the first, so we can avoid the last index)
-- For any h on a cycle, we can find an index i such that nodes[i]! = h and i+1 < length
theorem cycle_has_nonlast_index {S : AstroNet Hash} (p : AstroPath S)
    (hcyc : p.isCycle) (h : Hash) (hm : h ∈ p.nodes) :
    ∃ i, i + 1 < p.nodes.length ∧ p.nodes[i]! = h := by
  obtain ⟨⟨i, hi⟩, hget⟩ := List.mem_iff_get.mp hm
  rw [List.get_eq_getElem] at hget
  by_cases hi2 : i + 1 < p.nodes.length
  · refine ⟨i, hi2, ?_⟩
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hget
  · -- i is the last index
    have hi_last : i = p.nodes.length - 1 := by omega
    have hlen : p.nodes.length ≥ 2 := p.nonempty
    obtain ⟨hhl, _⟩ := hcyc
    have hne : p.nodes ≠ [] := by intro h'; simp [h'] at hlen
    have hhead : p.nodes.head? = some (p.nodes[0]'(by omega)) := by
      rw [List.head?_eq_some_head hne, List.head_eq_getElem]
    have hlast : p.nodes.getLast? = some (p.nodes[p.nodes.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
    rw [hhead, hlast] at hhl
    have heq := Option.some.inj hhl
    refine ⟨0, by omega, ?_⟩
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < p.nodes.length)]
    -- Goal: p.nodes[0] = h
    -- We know heq : p.nodes[0] = p.nodes[length-1] and hget : p.nodes[i] = h with i = length-1
    rw [heq]
    -- Goal: p.nodes[length-1] = h
    -- We have hget : p.nodes[↑⟨i, hi⟩] = h and hi_last : i = length-1
    convert hget using 2
    exact hi_last.symm

theorem cycle_node_successor (S : AstroNet Hash) (p : AstroPath S)
    (hcyc : p.isCycle) (h : Hash) (hm : h ∈ p.nodes) :
    ∃ e' ∈ S.entries, e'.id = h ∧ ∃ h' ∈ e'.ref, h' ∈ p.nodes := by
  obtain ⟨i, hi, hget⟩ := cycle_has_nonlast_index p hcyc h hm
  obtain ⟨e', he', hid, href⟩ := p.valid i hi
  have hid' : e'.id = h := by rw [← hget]; exact hid
  have h'_mem : p.nodes[i+1]! ∈ p.nodes := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  exact ⟨e', he', hid', p.nodes[i+1]!, href, h'_mem⟩

-- Helper: on a path, if nodes[i]! = e.id and e is an atom, then nodes[i+1]! = e.id
-- (provided i+1 < length)
theorem atom_path_step (S : AstroNet Hash) (p : AstroPath S) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hdeg : e.width = 0) (i : ℕ) (hi : i + 1 < p.nodes.length)
    (hid : p.nodes[i]! = e.id) : p.nodes[i+1]! = e.id := by
  have href := S.selfRef e he hdeg  -- e.ref = [e.id]
  obtain ⟨e', he', hid', hnext⟩ := p.valid i hi
  -- e'.id = nodes[i]! = e.id, so e' = e by injectivity
  have heq : e' = e := S.injectivity e' he' e he (by rw [hid', hid])
  rw [heq, href] at hnext
  -- hnext : nodes[i+1]! ∈ [e.id]
  rw [List.mem_singleton] at hnext
  exact hnext

-- All nodes on a path through an atom are the atom's id
-- Helper: from position i onward, all nodes are e.id (for atoms)
theorem atom_path_from (S : AstroNet Hash) (p : AstroPath S) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hdeg : e.width = 0) (i : ℕ)
    (_hi : i < p.nodes.length) (hid : p.nodes[i]! = e.id) :
    ∀ j, i ≤ j → j < p.nodes.length → p.nodes[j]! = e.id := by
  intro j hij hj
  induction hij with
  | refl => exact hid
  | step hle ih =>
    rename_i k
    have hk : k < p.nodes.length := by omega
    have hik := ih hk
    by_cases hk2 : k + 1 < p.nodes.length
    · exact atom_path_step S p e he hdeg k hk2 hik
    · omega

theorem atom_path_all_eq (S : AstroNet Hash) (p : AstroPath S) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hdeg : e.width = 0) (hcyc : p.isCycle) (hm : e.id ∈ p.nodes) :
    ∀ h, h ∈ p.nodes → h = e.id := by
  obtain ⟨i, hi, hget⟩ := cycle_has_nonlast_index p hcyc e.id hm
  have hlen : p.nodes.length ≥ 2 := p.nonempty
  have hne : p.nodes ≠ [] := by intro h'; simp [h'] at hlen
  -- All nodes from i to length-1 are e.id
  have hfrom := atom_path_from S p e he hdeg i (by omega) hget
  -- In particular, last node = e.id
  have hlast : p.nodes[p.nodes.length - 1]! = e.id :=
    hfrom (p.nodes.length - 1) (by omega) (by omega)
  -- Since cycle: head = last, so nodes[0] = e.id
  obtain ⟨hhl, _⟩ := hcyc
  have hhead_eq : p.nodes.head? = p.nodes.getLast? := hhl
  rw [List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne] at hhead_eq
  have hhead_last := Option.some.inj hhead_eq
  rw [List.head_eq_getElem, List.getLast_eq_getElem] at hhead_last
  -- hhead_last : p.nodes[0] = p.nodes[length-1]
  -- Convert hlast from getElem! to getElem
  have hlast' : p.nodes[p.nodes.length - 1]'(by omega) = e.id := by
    have := hlast
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have h0 : p.nodes[0]! = e.id := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp [hhead_last, hlast']
  -- Now all nodes from 0 to length-1 are e.id
  have hall := atom_path_from S p e he hdeg 0 (by omega) h0
  -- For any h ∈ nodes, h = e.id
  intro h hh
  obtain ⟨⟨j, hj⟩, hjget⟩ := List.mem_iff_get.mp hh
  rw [List.get_eq_getElem] at hjget
  have := hall j (by omega) hj
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj] at this
  simpa using this ▸ hjget.symm

-- Helper: atoms (stage 0) cannot be in cycles
theorem atom_not_inCycle (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hdeg : e.width = 0) : ¬ S.inCycle e := by
  intro ⟨p, hcyc, hm⟩
  obtain ⟨_, h_diff_mem, h_diff_ne⟩ := hcyc.2
  have hall := atom_path_all_eq S p e he hdeg hcyc hm
  have := hall _ h_diff_mem
  -- h_diff = e.id, but h_diff ≠ head?.get!
  -- We need head?.get! = e.id
  have hlen : p.nodes.length ≥ 2 := p.nonempty
  have hne : p.nodes ≠ [] := by intro h'; simp [h'] at hlen
  have : p.nodes.head?.get! = e.id := by
    rw [List.head?_eq_some_head hne]
    simp [Option.get!]
    rw [List.head_eq_getElem]
    exact hall (p.nodes[0]'(by omega)) (List.getElem_mem (by omega))
  exact absurd (this ▸ hall _ h_diff_mem) h_diff_ne

theorem depthFilt_not_inCycle (S : AstroNet Hash) (e : AstroNerve Hash)
    (n : ℕ) (hn : e ∈ depthFilt S n) : ¬ S.inCycle e := by
  induction n using Nat.strongRecOn generalizing e with
  | _ n ih =>
    intro hcyc
    obtain ⟨p, hpcyc, he_mem⟩ := hcyc
    have he_ent := depthFilt_sub_entries S n hn
    match n with
    | 0 =>
      have hdeg := depthFilt_zero_degree S e hn
      exact atom_not_inCycle S e he_ent hdeg ⟨p, hpcyc, he_mem⟩
    | Nat.succ k =>
      -- e ∈ depthFilt S (k+1), so all refs of e are ids of entries in depthFilt S k
      have href := depthFilt_succ_refs S e k hn
      -- e.id is on the cycle, so by cycle_node_successor, there's a ref h' also on the cycle
      obtain ⟨e'', he''_ent, he''_id, h', h'_ref, h'_mem⟩ :=
        cycle_node_successor S p hpcyc e.id he_mem
      -- e'' has id = e.id and is in S.entries, so e'' = e by injectivity
      have : e'' = e := S.injectivity e'' he''_ent e he_ent he''_id
      subst this
      -- h' ∈ e.ref and h' ∈ p.nodes
      -- By href, ∃ e_next ∈ depthFilt S k with e_next.id = h'
      obtain ⟨e_next, he_next_stage, he_next_id⟩ := href h' h'_ref
      -- e_next is in a cycle (same cycle p, since h' = e_next.id ∈ p.nodes)
      have h_next_cyc : S.inCycle e_next := by
        exact ⟨p, hpcyc, he_next_id ▸ h'_mem⟩
      -- By IH (k < k+1), e_next is not in a cycle
      exact ih k (Nat.lt_succ_of_le le_rfl) e_next he_next_stage h_next_cyc

-- Helper: given an unstaged entry, produce the next unstaged entry via a ref
-- The next entry's id is in the current entry's ref, and is distinct from the current entry's id
private noncomputable def nextUnstaged (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) :
    { e' : AstroNerve Hash // e' ∈ S.entries ∧ e'.id ∈ e.ref ∧ (∀ n, e' ∉ depthFilt S n) } := by
  have h := not_in_any_stage_has_unstaged_ref S e he hne
  -- h : ∃ r ∈ e.ref, ∃ e' ∈ S.entries, e'.id = r ∧ ∀ n, e' ∉ depthFilt S n
  -- Need to extract data from Prop to Type - use Classical.choice
  let r := h.choose
  have hr : r ∈ e.ref ∧ ∃ e' ∈ S.entries, e'.id = r ∧ ∀ n, e' ∉ depthFilt S n := by
    exact h.choose_spec
  let e' := hr.2.choose
  have he' : e' ∈ S.entries ∧ e'.id = r ∧ ∀ n, e' ∉ depthFilt S n := by
    exact hr.2.choose_spec
  exact ⟨e', he'.1, he'.2.1 ▸ hr.1, he'.2.2⟩

-- Build a sequence of unstaged entries
private noncomputable def unstagedSeq (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) :
    ℕ → { e' : AstroNerve Hash // e' ∈ S.entries ∧ (∀ n, e' ∉ depthFilt S n) }
  | 0 => ⟨e, he, hne⟩
  | n + 1 =>
    let prev := unstagedSeq S e he hne n
    let next := nextUnstaged S prev.1 prev.2.1 prev.2.2
    ⟨next.1, next.2.1, next.2.2.2⟩

-- The sequence has the ref property: seq(n+1).id ∈ seq(n).ref
omit [Inhabited Hash] in
private theorem unstagedSeq_ref (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) (n : ℕ) :
    (unstagedSeq S e he hne (n + 1)).1.id ∈ (unstagedSeq S e he hne n).1.ref := by
  simp [unstagedSeq]
  exact (nextUnstaged S (unstagedSeq S e he hne n).1
    (unstagedSeq S e he hne n).2.1 (unstagedSeq S e he hne n).2.2).2.2.1

-- All entries in the sequence are unstaged, hence have degree > 0
omit [Inhabited Hash] in
private theorem unstagedSeq_width_pos (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) (n : ℕ) :
    (unstagedSeq S e he hne n).1.width > 0 := by
  by_contra h
  push Not at h
  have := Nat.eq_zero_of_le_zero h
  have hmem := (unstagedSeq S e he hne n).2.1
  have hns := (unstagedSeq S e he hne n).2.2 0
  apply hns
  simp [depthFilt, Finset.mem_filter]
  exact ⟨hmem, this⟩

-- Consecutive entries in the sequence have distinct ids (by noSelfRef)
omit [Inhabited Hash] in
private theorem unstagedSeq_id_ne (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) (n : ℕ) :
    (unstagedSeq S e he hne (n + 1)).1.id ≠ (unstagedSeq S e he hne n).1.id := by
  intro heq
  have href := unstagedSeq_ref S e he hne n
  rw [heq] at href
  have hdeg := unstagedSeq_width_pos S e he hne n
  have hmem := (unstagedSeq S e he hne n).2.1
  exact S.noSelfRef _ hmem hdeg href

-- Pigeonhole: in a sequence of S.entries.card + 1 elements from S.entries,
-- two must have the same id
omit [Inhabited Hash] in
private theorem unstagedSeq_repeat (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) :
    ∃ i j, i < j ∧ j ≤ S.entries.card ∧
      (unstagedSeq S e he hne i).1.id = (unstagedSeq S e he hne j).1.id := by
  let s := Finset.range (S.entries.card + 1)
  let f : ℕ → Hash := fun i => (unstagedSeq S e he hne i).1.id
  have hcard : (Finset.image f s).card < s.card := by
    have h1 : (Finset.image f s).card ≤ (S.entries.image (fun e => e.id)).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_image] at hx ⊢
      obtain ⟨i, _, rfl⟩ := hx
      exact ⟨(unstagedSeq S e he hne i).1, (unstagedSeq S e he hne i).2.1, rfl⟩
    have h2 : (S.entries.image (fun e => e.id)).card ≤ S.entries.card :=
      Finset.card_image_le
    calc (Finset.image f s).card
        ≤ S.entries.card := le_trans h1 h2
      _ < S.entries.card + 1 := Nat.lt_succ_of_le le_rfl
      _ = s.card := by simp [s, Finset.card_range]
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_image_lt hcard
  simp [s] at hi hj
  by_cases h : i < j
  · exact ⟨i, j, h, by omega, heq⟩
  · exact ⟨j, i, by omega, by omega, heq.symm⟩

/-- Forward: entries on a cycle are never staged. -/
theorem inCycle_not_staged (S : AstroNet Hash) (e : AstroNerve Hash)
    (_he : e ∈ S.entries) (hcyc : S.inCycle e) :
    ∀ n, e ∉ depthFilt S n :=
  fun n hn => depthFilt_not_inCycle S e n hn hcyc

/-- From any unstaged entry, following refs reaches an entry on a cycle.
    Note: the unstaged entry itself may be on the "tail" leading to the cycle,
    not on the cycle itself (ρ-graph structure). -/
theorem unstaged_reaches_cycle (S : AstroNet Hash) (e : AstroNerve Hash)
    (he : e ∈ S.entries) (hne : ∀ n, e ∉ depthFilt S n) :
    ∃ (c : AstroNerve Hash), c ∈ S.entries ∧ (∀ n, c ∉ depthFilt S n) ∧ S.inCycle c := by
  -- Build the unstaged sequence and find a repeat via pigeonhole
  obtain ⟨i, j, hij, _hj, heq_id⟩ := unstagedSeq_repeat S e he hne
  -- The cycle is [seq[i].id, ..., seq[j].id]
  let c := (unstagedSeq S e he hne i).1
  refine ⟨c, (unstagedSeq S e he hne i).2.1, (unstagedSeq S e he hne i).2.2, ?_⟩
  -- Construct the cyclic path
  let nodes := (List.range (j - i + 1)).map (fun k => (unstagedSeq S e he hne (i + k)).1.id)
  have hlen : nodes.length = j - i + 1 := by simp [nodes]
  have hlen2 : nodes.length ≥ 2 := by simp [nodes]; omega
  have hfirst_last : nodes.head? = nodes.getLast? := by
    have hne_nodes : nodes ≠ [] := by intro h; simp [h] at hlen2
    rw [List.head?_eq_some_head hne_nodes, List.getLast?_eq_some_getLast hne_nodes]
    congr 1
    simp [List.head_eq_getElem, List.getLast_eq_getElem, nodes, List.getElem_map]
    have hij' : i + (j - i) = j := by omega
    rw [hij']; exact heq_id
  have hdistinct : ∃ h, h ∈ nodes ∧ h ≠ nodes.head?.get! := by
    have hne_nodes : nodes ≠ [] := by intro h; simp [h] at hlen2
    refine ⟨nodes[1]'(by omega), List.getElem_mem (by omega), ?_⟩
    rw [List.head?_eq_some_head hne_nodes]
    simp only [Option.get!, List.head_eq_getElem, nodes, List.getElem_map, List.getElem_range]
    exact unstagedSeq_id_ne S e he hne i
  have hvalid : ∀ idx, idx + 1 < nodes.length →
      ∃ e' ∈ S.entries, e'.id = nodes[idx]! ∧ nodes[idx+1]! ∈ e'.ref := by
    intro idx hidx
    simp [nodes] at hidx
    simp [nodes, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.getElem_range]
    refine ⟨(unstagedSeq S e he hne (i + idx)).1,
      (unstagedSeq S e he hne (i + idx)).2.1, rfl, ?_⟩
    have := unstagedSeq_ref S e he hne (i + idx)
    simp only [Nat.add_assoc] at this; exact this
  have hinStore : ∀ h, h ∈ nodes → ∃ e' ∈ S.entries, e'.id = h := by
    intro h hh; simp [nodes] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact ⟨(unstagedSeq S e he hne (i + k)).1,
      (unstagedSeq S e he hne (i + k)).2.1, rfl⟩
  let path : AstroPath S := ⟨nodes, hlen2, hvalid, hinStore⟩
  -- c.id = seq[i].id = nodes[0]
  have hc_in : c.id ∈ nodes := by
    show c.id ∈ nodes
    simp [nodes]
    exact ⟨0, by omega, by simp [c]⟩
  exact ⟨path, ⟨hfirst_last, hdistinct⟩, hc_in⟩

end Astrolabe
