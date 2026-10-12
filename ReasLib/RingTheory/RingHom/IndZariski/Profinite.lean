/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.ConnectedComponents
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

universe u v

open PrimeSpectrum

namespace RingHom.IndZariski

/-- A field admits an ind-Zariski extension whose prime spectrum realizes any
profinite topological space as a topological space. -/
theorem exists_of_profinite
    {k : Type u} [Field k] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (f : k →+* A) (e : PrimeSpectrum A ≃ₜ T),
      f.IndZariski :=
  sorry

end RingHom.IndZariski
