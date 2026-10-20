/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison

/-!
# Flattening morphisms of algebraic spaces by admissible blowups

A finite-type quasi-separated morphism of algebraic spaces that is flat and
locally of finite presentation over a quasi-compact open of a qcqs base becomes
flat and of finite presentation after an admissible blowup, on the strict transform.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type quasi-separated morphism of algebraic spaces over a quasi-compact
quasi-separated base, flat and locally of finite presentation over a quasi-compact
open, admits a blowup in a finitely presented closed center disjoint from that open
whose strict transform is flat and of finite presentation. -/
theorem exists_isAdmissibleBlowup_flat_finitePresentation
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f] [QuasiSeparated f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [Flat (pullback.snd f U.ι)]
    [LocallyOfFinitePresentation (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        let f' := strictTransformSnd b (Z.inverseImageSubspace b) f
        Flat f' ∧ FinitePresentation f' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
