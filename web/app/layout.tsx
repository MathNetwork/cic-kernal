import type { Metadata } from "next"
import { Geist_Mono } from "next/font/google"
import "./globals.css"

const mono = Geist_Mono({ variable: "--font-mono", subsets: ["latin"] })

export const metadata: Metadata = {
  title: "AstroCore — Content-Addressed CIC Kernel",
  description: "Interactive visualization: TreeKernel (names) vs HypergraphKernel (hashes)",
}

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className={`${mono.variable} antialiased`}>
      <body>{children}</body>
    </html>
  )
}
