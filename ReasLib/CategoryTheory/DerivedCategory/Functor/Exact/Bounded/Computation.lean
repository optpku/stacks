/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction

/-!
# Computation for bounded restrictions of exact derived functors

The bounded restrictions of an exact derived functor are full-subcategory
lifts.  This leaf records their object, morphism, and inclusion-comparison
normal forms so downstream developments need not unfold `ObjectProperty.lift`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus

namespace functor

/-- The underlying object of the bounded-below restriction is the image under
the ambient exact derived functor. -/
@[simp, stacks 015F "bounded-below exact derived functor object computation"]
theorem obj_obj (F : A ⥤ₑ B) (X : DerivedCategory.Plus A) :
    ((functor F).obj X).obj = F.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded-below restriction is the image
under the ambient exact derived functor. -/
@[simp, stacks 015F "bounded-below exact derived functor map computation"]
theorem map_hom (F : A ⥤ₑ B) {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    ((functor F).map f).hom = F.mapDerivedCategory.map f.hom := sorry

end functor

namespace compιIso

/-- The forward inclusion-comparison component for the bounded-below
restriction is the identity. -/
@[simp, stacks 015F "bounded-below exact derived inclusion comparison hom component"]
theorem hom_app (F : A ⥤ₑ B) (X : DerivedCategory.Plus A) :
    (compιIso F).hom.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

/-- The inverse inclusion-comparison component for the bounded-below
restriction is the identity. -/
@[simp, stacks 015F "bounded-below exact derived inclusion comparison inverse component"]
theorem inv_app (F : A ⥤ₑ B) (X : DerivedCategory.Plus A) :
    (compιIso F).inv.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

end compιIso

end Plus

namespace Minus

namespace functor

/-- The underlying object of the bounded-above restriction is the image under
the ambient exact derived functor. -/
@[simp, stacks 015F "bounded-above exact derived functor object computation"]
theorem obj_obj (F : A ⥤ₑ B) (X : DerivedCategory.Minus A) :
    ((functor F).obj X).obj = F.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded-above restriction is the image
under the ambient exact derived functor. -/
@[simp, stacks 015F "bounded-above exact derived functor map computation"]
theorem map_hom (F : A ⥤ₑ B) {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) :
    ((functor F).map f).hom = F.mapDerivedCategory.map f.hom := sorry

end functor

namespace compιIso

/-- The forward inclusion-comparison component for the bounded-above
restriction is the identity. -/
@[simp, stacks 015F "bounded-above exact derived inclusion comparison hom component"]
theorem hom_app (F : A ⥤ₑ B) (X : DerivedCategory.Minus A) :
    (compιIso F).hom.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

/-- The inverse inclusion-comparison component for the bounded-above
restriction is the identity. -/
@[simp, stacks 015F "bounded-above exact derived inclusion comparison inverse component"]
theorem inv_app (F : A ⥤ₑ B) (X : DerivedCategory.Minus A) :
    (compιIso F).inv.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

end compιIso

end Minus

namespace Bounded

namespace functor

/-- The underlying object of the bounded restriction is the image under the
ambient exact derived functor. -/
@[simp, stacks 015F "bounded exact derived functor object computation"]
theorem obj_obj (F : A ⥤ₑ B) (X : DerivedCategory.Bounded A) :
    ((functor F).obj X).obj = F.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded restriction is the image under the
ambient exact derived functor. -/
@[simp, stacks 015F "bounded exact derived functor map computation"]
theorem map_hom (F : A ⥤ₑ B) {X Y : DerivedCategory.Bounded A} (f : X ⟶ Y) :
    ((functor F).map f).hom = F.mapDerivedCategory.map f.hom := sorry

end functor

namespace compιIso

/-- The forward inclusion-comparison component for the bounded restriction is
the identity. -/
@[simp, stacks 015F "bounded exact derived inclusion comparison hom component"]
theorem hom_app (F : A ⥤ₑ B) (X : DerivedCategory.Bounded A) :
    (compιIso F).hom.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

/-- The inverse inclusion-comparison component for the bounded restriction is
the identity. -/
@[simp, stacks 015F "bounded exact derived inclusion comparison inverse component"]
theorem inv_app (F : A ⥤ₑ B) (X : DerivedCategory.Bounded A) :
    (compιIso F).inv.app X = 𝟙 (F.mapDerivedCategory.obj X.obj) := sorry

end compιIso

end Bounded

end CategoryTheory.ExactFunctor.Derived
