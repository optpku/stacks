/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Reduction
import StacksCheckRecall

/-!
# Example 87.12.2

If `A` is a weakly admissible topological ring, then the reduction of
`Spf(A)` is `Spec(A ⧸ a)`, where `a` is the ideal of topologically nilpotent
elements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Example 87.12.2

The checked comparison identifies `Spec(A ⧸ topologicalNilradical A)` with
the independently defined reduction of the formal spectrum. -/
@[stacks 0GB6] #check
  (AlgebraicGeometry.FormalSpectrum.isIso_toReduction :
    ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
      (structureHom : Spec (.of A) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
      IsIso (AlgebraicGeometry.FormalSpectrum.toReduction A structureHom))
