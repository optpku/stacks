module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Derived Single-Object Comparisons

This module compares single objects with the functors on bounded homotopy
categories induced by an additive functor.  The three boundedness variants
share the variance-neutral comparison `Functor.Homotopy.singleIso` and expose
the same all-degree API.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Preadditive A] [HasZeroObject A]
  [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

namespace toBoundedBelowDerived

/-- The functor induced on `K⁺` carries a single object in degree `n` to the
corresponding derived single object after inclusion in the ambient category. -/
@[stacks 015A]
noncomputable def singleIso (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor A n ⋙ F.toBoundedBelowDerived ⋙
        DerivedCategory.Plus.ι ≅
      F ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor A n)
      (toBoundedBelowDerived.compInclusionIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Plus.singleFunctorCompιIso A n)
        (Functor.Homotopy.toDerived F) ≪≫
      Functor.Homotopy.singleIso F n

namespace singleIso

/-- Naturality of the forward bounded-below single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single comparison naturality"]
theorem hom_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (HomotopyCategory.Plus.singleFunctor A n ⋙ F.toBoundedBelowDerived ⋙
        DerivedCategory.Plus.ι).map f ≫
      (toBoundedBelowDerived.singleIso F n).hom.app Y =
        (toBoundedBelowDerived.singleIso F n).hom.app X ≫
          (F ⋙ DerivedCategory.singleFunctor B n).map f := sorry

/-- Naturality of the inverse bounded-below single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single comparison naturality"]
theorem inv_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (F ⋙ DerivedCategory.singleFunctor B n).map f ≫
      (toBoundedBelowDerived.singleIso F n).inv.app Y =
        (toBoundedBelowDerived.singleIso F n).inv.app X ≫
          (HomotopyCategory.Plus.singleFunctor A n ⋙ F.toBoundedBelowDerived ⋙
            DerivedCategory.Plus.ι).map f := sorry

end singleIso

end toBoundedBelowDerived

namespace toBoundedAboveDerived

/-- The functor induced on `K⁻` carries a single object in degree `n` to the
corresponding derived single object after inclusion in the ambient category. -/
@[stacks 015A]
noncomputable def singleIso (n : ℤ) :
    HomotopyCategory.Minus.singleFunctor A n ⋙
        F.toBoundedAboveDerived ⋙ DerivedCategory.Minus.ι ≅
      F ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerLeft (HomotopyCategory.Minus.singleFunctor A n)
      (toBoundedAboveDerived.compInclusionIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Minus.singleFunctorCompιIso A n)
        (Functor.Homotopy.toDerived F) ≪≫
      Functor.Homotopy.singleIso F n

namespace singleIso

/-- Naturality of the forward bounded-above single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single comparison naturality"]
theorem hom_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (HomotopyCategory.Minus.singleFunctor A n ⋙
        F.toBoundedAboveDerived ⋙ DerivedCategory.Minus.ι).map f ≫
      (toBoundedAboveDerived.singleIso F n).hom.app Y =
        (toBoundedAboveDerived.singleIso F n).hom.app X ≫
          (F ⋙ DerivedCategory.singleFunctor B n).map f := sorry

/-- Naturality of the inverse bounded-above single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single comparison naturality"]
theorem inv_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (F ⋙ DerivedCategory.singleFunctor B n).map f ≫
      (toBoundedAboveDerived.singleIso F n).inv.app Y =
        (toBoundedAboveDerived.singleIso F n).inv.app X ≫
          (HomotopyCategory.Minus.singleFunctor A n ⋙
            F.toBoundedAboveDerived ⋙ DerivedCategory.Minus.ι).map f := sorry

end singleIso

end toBoundedAboveDerived

namespace toBoundedDerived

/-- The functor induced on `Kᵇ` carries a single object in degree `n` to the
corresponding derived single object after inclusion in the ambient category. -/
@[stacks 0FCP]
noncomputable def singleIso (n : ℤ) :
    HomotopyCategory.Bounded.singleFunctor A n ⋙
        F.toBoundedDerived ⋙ DerivedCategory.Bounded.ι ≅
      F ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerLeft (HomotopyCategory.Bounded.singleFunctor A n)
      (toBoundedDerived.compInclusionIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Bounded.singleFunctorCompιIso A n)
        (Functor.Homotopy.toDerived F) ≪≫
      Functor.Homotopy.singleIso F n

namespace singleIso

/-- Naturality of the forward bounded single-object comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single comparison naturality"]
theorem hom_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (HomotopyCategory.Bounded.singleFunctor A n ⋙
        F.toBoundedDerived ⋙ DerivedCategory.Bounded.ι).map f ≫
      (toBoundedDerived.singleIso F n).hom.app Y =
        (toBoundedDerived.singleIso F n).hom.app X ≫
          (F ⋙ DerivedCategory.singleFunctor B n).map f := sorry

/-- Naturality of the inverse bounded single-object comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single comparison naturality"]
theorem inv_naturality (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (F ⋙ DerivedCategory.singleFunctor B n).map f ≫
      (toBoundedDerived.singleIso F n).inv.app Y =
        (toBoundedDerived.singleIso F n).inv.app X ≫
          (HomotopyCategory.Bounded.singleFunctor A n ⋙
            F.toBoundedDerived ⋙ DerivedCategory.Bounded.ι).map f := sorry

end singleIso

end toBoundedDerived



end CategoryTheory.Functor
