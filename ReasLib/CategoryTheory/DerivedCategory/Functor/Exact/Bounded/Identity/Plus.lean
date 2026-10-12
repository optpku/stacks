/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Identity.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity exact functors on bounded-below derived categories

The generic restricted identity comparison specializes to the bounded-below
derived category, with objectwise and underlying-component readouts.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.ExactFunctor.Derived.Plus

variable (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- The exact derived action preserves the identity functor on the
bounded-below derived category. -/
@[stacks 015F "bounded-below exact derived action preserves identity"]
noncomputable def idFunctorIso :
    functor (ExactFunctor.id A) ≅ Functor.id (DerivedCategory.Plus A) :=
  Restriction.idFunctorIso A (t.plus : ObjectProperty (DerivedCategory A))
    (mapsTo (ExactFunctor.id A))

/-- The objectwise identity comparison for the exact derived action on the
bounded-below derived category. -/
@[stacks 015F "bounded-below exact derived identity comparison"]
noncomputable abbrev idObjIso (X : DerivedCategory.Plus A) :
    (functor (ExactFunctor.id A)).obj X ≅ X :=
  (idFunctorIso A).app X

/-- Naturality of the objectwise identity comparison on the bounded-below
derived category. -/
@[reassoc]
theorem idObjIso_naturality {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    (functor (ExactFunctor.id A)).map f ≫ (idObjIso A Y).hom =
      (idObjIso A X).hom ≫ f := sorry

namespace idFunctorIso

/-- The components of the bounded-below identity comparison are the
objectwise comparisons. -/
@[simp]
theorem app (X : DerivedCategory.Plus A) :
    (idFunctorIso A).app X = idObjIso A X := sorry

/-- Forgetting bounded-below structure identifies the forward component with
the ambient exact-derived identity comparison. -/
@[simp, stacks 015F "bounded-below identity comparison forward component"]
theorem hom_app_hom (X : DerivedCategory.Plus A) :
    ((idFunctorIso A).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.idObjIso A X.obj).hom := sorry

/-- Forgetting bounded-below structure identifies the inverse component with
the ambient exact-derived identity comparison. -/
@[simp, stacks 015F "bounded-below identity comparison inverse component"]
theorem inv_app_hom (X : DerivedCategory.Plus A) :
    ((idFunctorIso A).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.idObjIso A X.obj).inv := sorry

end idFunctorIso

end CategoryTheory.ExactFunctor.Derived.Plus
