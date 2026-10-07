module

public import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computation for Bounded Derived Serre Quotients

The boundedness restrictions of a derived Serre quotient are full-subcategory
lifts.  This leaf exposes their object and morphism normal forms without
requiring downstream users to unfold `ObjectProperty.lift`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe wA wQ vA uA

namespace CategoryTheory.ObjectProperty.SerreClassLocalization.Derived

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} P.isoModSerre.Localization]

namespace Plus.Quotient.functor

/-- The underlying object of the bounded-below derived Serre quotient is its
ordinary derived quotient image. -/
@[simp, stacks 06XM "bounded-below derived Serre quotient object computation"]
theorem obj_obj (X : DerivedCategory.Plus A) :
    ((Plus.Quotient.functor P).obj X).obj =
      P.isoModSerre.Q.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded-below derived Serre quotient is
its ordinary derived quotient map. -/
@[simp, stacks 06XM "bounded-below derived Serre quotient map computation"]
theorem map_hom {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    ((Plus.Quotient.functor P).map f).hom =
      P.isoModSerre.Q.mapDerivedCategory.map f.hom := sorry

end Plus.Quotient.functor

namespace Minus.Quotient.functor

/-- The underlying object of the bounded-above derived Serre quotient is its
ordinary derived quotient image. -/
@[simp, stacks 06XM "bounded-above derived Serre quotient object computation"]
theorem obj_obj (X : DerivedCategory.Minus A) :
    ((Minus.Quotient.functor P).obj X).obj =
      P.isoModSerre.Q.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded-above derived Serre quotient is
its ordinary derived quotient map. -/
@[simp, stacks 06XM "bounded-above derived Serre quotient map computation"]
theorem map_hom {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) :
    ((Minus.Quotient.functor P).map f).hom =
      P.isoModSerre.Q.mapDerivedCategory.map f.hom := sorry

end Minus.Quotient.functor

namespace Bounded.Quotient.functor

/-- The underlying object of the bounded derived Serre quotient is its
ordinary derived quotient image. -/
@[simp, stacks 06XM "bounded derived Serre quotient object computation"]
theorem obj_obj (X : DerivedCategory.Bounded A) :
    ((Bounded.Quotient.functor P).obj X).obj =
      P.isoModSerre.Q.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded derived Serre quotient is its
ordinary derived quotient map. -/
@[simp, stacks 06XM "bounded derived Serre quotient map computation"]
theorem map_hom {X Y : DerivedCategory.Bounded A} (f : X ⟶ Y) :
    ((Bounded.Quotient.functor P).map f).hom =
      P.isoModSerre.Q.mapDerivedCategory.map f.hom := sorry

end Bounded.Quotient.functor

end CategoryTheory.ObjectProperty.SerreClassLocalization.Derived
