module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition Comparisons for Left Derived Functors

This file constructs the comparison from a composite of two chosen left derived models to a
chosen model of the composite. The construction is neutral in both localization functors and
does not require the two intermediate models themselves to satisfy a universal property.
-/

universe vA vB vC vDA vDB uA uB uC uDA uDB

namespace CategoryTheory

namespace Functor

namespace LeftDerived.Composition

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {DA : Type uDA} {DB : Type uDB}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vDA} DA] [Category.{vDB} DB]
  {F : A ⥤ B} {G : B ⥤ C} {L : A ⥤ DA} {L' : B ⥤ DB}
  {LF : DA ⥤ DB} {LG : DB ⥤ C} {LGF : DA ⥤ C}

/-- The counit obtained by composing chosen left-derived model data for F and G. -/
def iteratedCounit
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G) :
    L ⋙ (LF ⋙ LG) ⟶ F ⋙ G :=
  (associator L LF LG).inv ≫
    whiskerRight εF LG ≫
    (associator F L' LG).hom ≫
    whiskerLeft F εG

set_option backward.isDefEq.respectTransparency false in
/-- The component of the iterated left-derived counit is the composite of the two counit
components. -/
@[simp]
theorem iteratedCounit_app
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (X : A) :
    (iteratedCounit εF εG).app X =
      LG.map (εF.app X) ≫ εG.app (F.obj X) := by
  simp [iteratedCounit]

/-- The comparison from the composite of chosen models of F and G to a chosen left-derived
model of F ⋙ G. Only the model of F ⋙ G must satisfy the universal property. -/
@[stacks 05T2]
noncomputable def comparisonOfModels
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S]
    [LGF.IsLeftDerivedFunctor εGF S] :
    LF ⋙ LG ⟶ LGF :=
  LGF.leftDerivedLift εGF S (LF ⋙ LG) (iteratedCounit εF εG)

/-- The left-derived model comparison followed by the direct counit is the iterated counit. -/
@[reassoc (attr := simp)]
theorem comparisonOfModels_fac
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S]
    [LGF.IsLeftDerivedFunctor εGF S] :
    whiskerLeft L (comparisonOfModels S εF εG εGF) ≫ εGF =
      iteratedCounit εF εG := by
  exact LGF.leftDerived_fac εGF S (LF ⋙ LG) (iteratedCounit εF εG)

/-- The componentwise factorization equation for the left-derived model comparison. -/
theorem comparisonOfModels_fac_app
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S]
    [LGF.IsLeftDerivedFunctor εGF S]
    (X : A) :
    (comparisonOfModels S εF εG εGF).app (L.obj X) ≫ εGF.app X =
      (iteratedCounit εF εG).app X := by
  exact LGF.leftDerived_fac_app εGF S (LF ⋙ LG) (iteratedCounit εF εG) X

set_option backward.isDefEq.respectTransparency false in
/-- At an object represented by the localization functor, invertibility of the comparison is
equivalent to invertibility of the iterated counit when the direct counit is invertible. -/
theorem comparisonOfModels_app_isIso_iff
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S]
    [LGF.IsLeftDerivedFunctor εGF S]
    (X : A)
    [IsIso (εGF.app X)] :
    IsIso ((comparisonOfModels S εF εG εGF).app (L.obj X)) ↔
      IsIso ((iteratedCounit εF εG).app X) := by
  rw [← comparisonOfModels_fac_app S εF εG εGF X]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Invertible component counits make the left-derived model comparison invertible at the
corresponding localized object. -/
instance comparisonOfModels_app_isIso
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L')
    (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S]
    [LGF.IsLeftDerivedFunctor εGF S]
    (X : A)
    [IsIso (εF.app X)]
    [IsIso (εG.app (F.obj X))]
    [IsIso (εGF.app X)] :
    IsIso ((comparisonOfModels S εF εG εGF).app (L.obj X)) := by
  rw [comparisonOfModels_app_isIso_iff S εF εG εGF X, iteratedCounit_app]
  infer_instance

end LeftDerived.Composition

end Functor

end CategoryTheory
