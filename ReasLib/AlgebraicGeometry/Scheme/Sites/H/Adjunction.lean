/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.DerivedComparison

/-!
# Abelian and derived h-to-étale adjunctions

The abelian direct image from the big h slice to the small étale site is the composite
`ε_{X,*} ⋙ π_{X,*}`. Its bounded-below derived adjunction has invertible unit on complexes
with locally torsion cohomology sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Direct image `a_{X,*}` on abelian sheaves from the big h slice `(Sch/X)_h` to the small
étale site of `X`. -/
def aPushforward (X : Scheme.{u}) :
    Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb etale_le_h X ⋙
    AlgebraicGeometry.Scheme.FppfEtale.piPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq (X : Scheme.{u}) :
    aPushforward X = comparisonTopologyPushforwardAb etale_le_h X ⋙
      AlgebraicGeometry.Scheme.FppfEtale.piPushforward X := rfl

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive (X : Scheme.{u}) : (aPushforward X).Additive :=
  inferInstanceAs
    ((comparisonTopologyPushforwardAb etale_le_h X ⋙
      AlgebraicGeometry.Scheme.FppfEtale.piPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction (X : Scheme.{u}) : aInverseImage X ⊣ aPushforward X :=
  (AlgebraicGeometry.Scheme.FppfEtale.piAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq (X : Scheme.{u}) :
    aAdjunction X =
      (AlgebraicGeometry.Scheme.FppfEtale.piAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X) := rfl

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor (X : Scheme.{u}) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward (X : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq (X : Scheme.{u}) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) := rfl

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction (X : Scheme.{u}) :
    plusAInverseImage X ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq (X : Scheme.{u}) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
        (aPushforward X) (aAdjunction X) := rfl

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism on locally torsion
abelian sheaves. -/
theorem aAdjunction_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q` on locally torsion abelian
sheaves. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseImage X).obj F)) := sorry

/-- For a scheme `X` and a bounded-below complex of small étale abelian sheaves with locally
torsion cohomology, the derived h-to-étale adjunction unit `K ⟶ Ra_{X,*} (a_X⁻¹ K)` is an
isomorphism. -/
@[stacks 0EWG]
theorem plusAAdjunction_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusAAdjunction X).unit.app K) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end

