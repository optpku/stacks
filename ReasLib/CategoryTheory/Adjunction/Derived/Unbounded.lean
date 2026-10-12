/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded derived adjunctions with an exact left adjoint

An exact left adjoint acts directly on unbounded derived categories.  For a Grothendieck-abelian
source of the right adjoint, the K-injective total right-derived owner supplies the right-hand
functor and its unit.  The only nonformal input is the absolute-derived pair condition required by
the general derived-adjunction theorem; the K-injective specialization installs that condition as
a named instance so callers do not rebuild proof-local `let` declarations.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe uC uD vC vD wC wD

namespace CategoryTheory.Adjunction.Derived.KInjective

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- The exact left action on an unbounded derived category. -/
@[stacks 015F "exact left action on unbounded derived categories"]
noncomputable abbrev left (L : C ⥤ₑ D) :
    DerivedCategory C ⥤ DerivedCategory D :=
  L.obj.mapDerivedCategory

/-- The K-injective total right-derived action of an additive functor. -/
@[stacks 05TH "K-injective unbounded right-derived action"]
noncomputable abbrev right (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    DerivedCategory D ⥤ DerivedCategory C :=
  Functor.RightDerived.KInjective.functor R

/-- The localization factor of the exact left action. -/
@[stacks 015F "exact left derived factor"]
noncomputable abbrev leftFactor (L : C ⥤ₑ D) :
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙ left L ⟶
      L.obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) :=
  L.obj.mapDerivedCategoryFactors.hom

/-- The cochain-level unit of the K-injective total right-derived action. -/
@[stacks 05TH "K-injective right-derived unit"]
noncomputable abbrev rightUnit (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    R.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⟶
      (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) ⋙ right R :=
  Functor.RightDerived.KInjective.unit R

/-- The exact left action is a left-derived functor of its homotopy action. -/
@[stacks 015F "exact action is left derived", instance]
noncomputable instance left_isLeftDerived (L : C ⥤ₑ D) :
    (left L).IsLeftDerivedFunctor (leftFactor L)
      (HomologicalComplex.quasiIso C (up ℤ)) := sorry

/-- The K-injective action is a right-derived functor of the homotopy action. -/
@[stacks 05TH "K-injective action is right derived", instance]
noncomputable instance right_isRightDerived (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    (right R).IsRightDerivedFunctor (rightUnit R)
      (HomologicalComplex.quasiIso D (up ℤ)) := sorry

/-- The structure map for deriving the composite of the exact left action and the right action. -/
@[stacks 015F "exact-left/right-derived composite factor"]
noncomputable abbrev leftRightFactor (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙
        (left L ⋙ right R) ⟶
      (L.obj.mapHomologicalComplex (up ℤ) ⋙
          (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)) ⋙ right R :=
  (Functor.associator (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
      (left L) (right R)).inv ≫
    Functor.whiskerRight (leftFactor L) (right R)

/-- The structure map for deriving the composite of the right action and the exact left action. -/
@[stacks 05TH "right-derived/exact-left composite unit"]
noncomputable abbrev rightLeftUnit (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    (R.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)) ⋙ left L ⟶
      (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) ⋙
        (right R ⋙ left L) :=
  Functor.whiskerRight (rightUnit R) (left L) ≫
    (Functor.associator (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
      (right R) (left L)).hom

/-- The absolute-derived pair needed by the unbounded derived-adjunction construction. -/
@[stacks 015F "absolute unbounded derived pair"]
class HasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] : Prop where
  /-- The exact-left/right-derived composite remains left derived. -/
  leftRight :
    (left L ⋙ right R).IsLeftDerivedFunctor (leftRightFactor L R)
      (HomologicalComplex.quasiIso C (up ℤ))
  /-- The right-derived/exact-left composite remains right derived. -/
  rightLeft :
    (right R ⋙ left L).IsRightDerivedFunctor (rightLeftUnit L R)
      (HomologicalComplex.quasiIso D (up ℤ))

attribute [instance] HasPair.leftRight HasPair.rightLeft

/-- K-injective resolutions provide the absolute-derived pair for an exact adjoint. -/
@[stacks 05TH "canonical K-injective absolute-derived pair", instance]
noncomputable instance hasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] : HasPair L R := sorry

/-- The unbounded derived adjunction associated to an exact/K-injective adjoint pair. -/
@[stacks 05TH "unbounded derived adjunction for an exact left adjoint"]
noncomputable def adjunction (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] (adj : L.obj ⊣ R) :
    left L ⊣ right R :=
  @CategoryTheory.Adjunction.derived
    _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction adj (up ℤ))
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
    (HomologicalComplex.quasiIso C (up ℤ))
    (HomologicalComplex.quasiIso D (up ℤ))
    inferInstance inferInstance
    (left L) (right R) (leftFactor L) (rightUnit R)
    (left_isLeftDerived L) (right_isRightDerived R)
    (HasPair.leftRight (L := L) (R := R))
    (HasPair.rightLeft (L := L) (R := R))

end CategoryTheory.Adjunction.Derived.KInjective

end
