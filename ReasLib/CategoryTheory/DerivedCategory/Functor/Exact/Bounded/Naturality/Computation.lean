/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for functorial bounded exact-derived restrictions

This leaf records the object and morphism actions of the functorial bounded
restrictions, together with the components of restricted natural
isomorphisms.  All statements specialize the generic full-subcategory
restriction API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus.mapFunctor

/-- The functorial bounded-below action sends an exact functor to its
bounded-below restriction. -/
@[simp, stacks 015F "bounded-below exact-derived action on functors"]
theorem obj (F : A ⥤ₑ B) :
    (Plus.mapFunctor A B).obj F = Plus.functor F := sorry

/-- The functorial bounded-below action sends an exact natural transformation
to its bounded-below restriction. -/
@[simp, stacks 015F "bounded-below exact-derived action on transformations"]
theorem map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    (Plus.mapFunctor A B).map α = Plus.map α := sorry

end Plus.mapFunctor

namespace Plus.mapIso

/-- The underlying forward component of a bounded-below exact-derived
isomorphism is the ambient derived component. -/
@[simp, stacks 015F "bounded-below exact-derived isomorphism forward component"]
theorem hom_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Plus A) :
    ((Plus.mapIso e).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.hom).app X.obj := sorry

/-- The underlying inverse component of a bounded-below exact-derived
isomorphism is the ambient derived component. -/
@[simp, stacks 015F "bounded-below exact-derived isomorphism inverse component"]
theorem inv_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Plus A) :
    ((Plus.mapIso e).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.inv).app X.obj := sorry

end Plus.mapIso

namespace Minus.mapFunctor

/-- The functorial bounded-above action sends an exact functor to its
bounded-above restriction. -/
@[simp, stacks 015F "bounded-above exact-derived action on functors"]
theorem obj (F : A ⥤ₑ B) :
    (Minus.mapFunctor A B).obj F = Minus.functor F := sorry

/-- The functorial bounded-above action sends an exact natural transformation
to its bounded-above restriction. -/
@[simp, stacks 015F "bounded-above exact-derived action on transformations"]
theorem map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    (Minus.mapFunctor A B).map α = Minus.map α := sorry

end Minus.mapFunctor

namespace Minus.mapIso

/-- The underlying forward component of a bounded-above exact-derived
isomorphism is the ambient derived component. -/
@[simp, stacks 015F "bounded-above exact-derived isomorphism forward component"]
theorem hom_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Minus A) :
    ((Minus.mapIso e).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.hom).app X.obj := sorry

/-- The underlying inverse component of a bounded-above exact-derived
isomorphism is the ambient derived component. -/
@[simp, stacks 015F "bounded-above exact-derived isomorphism inverse component"]
theorem inv_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Minus A) :
    ((Minus.mapIso e).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.inv).app X.obj := sorry

end Minus.mapIso

namespace Bounded.mapFunctor

/-- The functorial bounded action sends an exact functor to its bounded
restriction. -/
@[simp, stacks 015F "bounded exact-derived action on functors"]
theorem obj (F : A ⥤ₑ B) :
    (Bounded.mapFunctor A B).obj F = Bounded.functor F := sorry

/-- The functorial bounded action sends an exact natural transformation to its
bounded restriction. -/
@[simp, stacks 015F "bounded exact-derived action on transformations"]
theorem map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    (Bounded.mapFunctor A B).map α = Bounded.map α := sorry

end Bounded.mapFunctor

namespace Bounded.mapIso

/-- The underlying forward component of a bounded exact-derived isomorphism
is the ambient derived component. -/
@[simp, stacks 015F "bounded exact-derived isomorphism forward component"]
theorem hom_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Bounded A) :
    ((Bounded.mapIso e).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.hom).app X.obj := sorry

/-- The underlying inverse component of a bounded exact-derived isomorphism
is the ambient derived component. -/
@[simp, stacks 015F "bounded exact-derived isomorphism inverse component"]
theorem inv_app_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    (X : DerivedCategory.Bounded A) :
    ((Bounded.mapIso e).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.map e.inv).app X.obj := sorry

end Bounded.mapIso

end CategoryTheory.ExactFunctor.Derived
