/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison

/-!
# Finite locally free strict transforms of algebraic spaces

Proper morphisms that are finite locally free over a quasi-compact open admit
finite locally free strict transforms after admissible blowups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism to a quasi-compact quasi-separated algebraic space that is
finite locally free over a quasi-compact open has a finite locally free strict
transform after a blowup in a finitely presented closed center disjoint from
that open. -/
theorem exists_isAdmissibleBlowup_finiteLocallyFree
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [FiniteLocallyFree (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        FiniteLocallyFree (strictTransformSnd b (Z.inverseImageSubspace b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
