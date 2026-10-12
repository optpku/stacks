/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms

@[expose] public section

/-!
# Functoriality of Filtered Objects

This module constructs the filtration obtained by mapping every filtration subobject through a
functor which preserves monomorphisms.  Finiteness needs only preservation of zero morphisms, so
it is deliberately separate from left exactness.  The core APIs are
`IndexedFiltration.map`, `FilteredObject.mapFunctor`, and
`FilteredObject.Finite.mapFunctor`.
-/

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace IndexedFiltration

section Map

variable (F : C ⥤ D) [F.PreservesMonomorphisms]
variable {I : Type w} [Preorder I]

/-- Stacks 015S: mapping each filtration subobject through a mono-preserving functor preserves
the indexed-filtration order. -/
@[stacks 015S]
theorem map_monotone {A : C} (filtration : IndexedFiltration I A) :
    Monotone (fun i : Iᵒᵈ ↦ Subobject.mk (F.map (filtration i).arrow)) := sorry

/-- Stacks 015S: the indexed filtration on `F.obj A` obtained by applying `F` to every filtration
subobject of `A`. -/
@[stacks 015S]
noncomputable def map {A : C} (filtration : IndexedFiltration I A) :
    IndexedFiltration I (F.obj A) where
  toFun := fun i ↦ Subobject.mk (F.map (filtration i).arrow)
  monotone' := map_monotone F filtration

/-- The `i`-th stage of a mapped filtration is the image of the original `i`-th stage under
the ambient functor. -/
@[simp]
theorem map_stage {A : C} (filtration : IndexedFiltration I A) (i : I) :
    (map F filtration).stage i = Subobject.mk (F.map (filtration.stage i).arrow) := sorry

end Map

section Top

variable (F : C ⥤ D) [F.PreservesMonomorphisms]
variable {I : Type w} [Preorder I]

/-- A top filtration stage remains top after applying a mono-preserving functor. -/
theorem map_eq_top {A : C} (filtration : IndexedFiltration I A) {i : I}
    (h : filtration.stage i = ⊤) :
    (map F filtration).stage i = ⊤ := sorry

end Top

section Bottom

variable (F : C ⥤ D) [F.PreservesMonomorphisms]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] [F.PreservesZeroMorphisms]
variable {I : Type w} [Preorder I]

/-- A bottom filtration stage remains bottom after applying a zero-preserving functor. -/
theorem map_eq_bot {A : C} (filtration : IndexedFiltration I A) {i : I}
    (h : filtration.stage i = ⊥) :
    (map F filtration).stage i = ⊥ := sorry

end Bottom

end IndexedFiltration

namespace FilteredObject

section Map

variable (F : C ⥤ D) [F.PreservesMonomorphisms]

/-- Stacks 015S: applying a mono-preserving functor to the underlying object and every
filtration subobject. -/
@[stacks 015S]
noncomputable def map (A : FilteredObject C) : FilteredObject D where
  obj := F.obj A.obj
  filtration := IndexedFiltration.map F A.filtration

namespace Hom

/-- Stacks 015S: a filtration-preserving morphism remains filtration-preserving after applying a
mono-preserving functor. -/
@[stacks 015S]
theorem map_preserves {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    ((FilteredObject.map F B).filtration p).Factors
      (((FilteredObject.map F A).filtration p).arrow ≫ F.map f.hom) := sorry

/-- Stacks 015S: the morphism of mapped filtered objects induced by a filtration-preserving
morphism. -/
@[stacks 015S]
noncomputable def map {A B : FilteredObject C} (f : A ⟶ B) :
    FilteredObject.map F A ⟶ FilteredObject.map F B where
  hom := F.map f.hom
  preserves := map_preserves F f

/-- The image of an identity filtered morphism is the identity. -/
@[stacks 015S]
theorem map_id (A : FilteredObject C) :
    map F (𝟙 A) = 𝟙 (FilteredObject.map F A) := sorry

/-- Mapping filtered morphisms respects composition. -/
@[stacks 015S]
theorem map_comp {A B E : FilteredObject C} (f : A ⟶ B) (g : B ⟶ E) :
    map F (f ≫ g) = map F f ≫ map F g := sorry

end Hom

/-- Stacks 015S: the functor induced on filtered objects by a mono-preserving functor. -/
@[stacks 015S]
noncomputable def mapFunctor : FilteredObject C ⥤ FilteredObject D where
  obj A := FilteredObject.map F A
  map f := Hom.map F f
  map_id A := Hom.map_id F A
  map_comp f g := Hom.map_comp F f g

end Map

section ZeroMorphisms

variable (F : C ⥤ D) [F.PreservesMonomorphisms]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- The functor on filtered objects induced by a zero-preserving mono-preserving
functor preserves zero morphisms. -/
instance mapFunctor_preservesZeroMorphisms [F.PreservesZeroMorphisms] :
    (mapFunctor F).PreservesZeroMorphisms := sorry

end ZeroMorphisms

section Finite

variable (F : C ⥤ D) [F.PreservesMonomorphisms]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] [F.PreservesZeroMorphisms]

namespace Finite

/-- Stacks 015S: a mono- and zero-preserving functor sends finite filtered objects to finite
filtered objects. -/
@[stacks 015S]
theorem map_isFinite {A : FilteredObject C} (hA : A.IsFinite) :
    (FilteredObject.map F A).IsFinite := sorry

/-- Stacks 015S: the functor induced by `F` on the full subcategories of finite filtered
objects. -/
@[stacks 015S]
noncomputable def mapFunctor :
    FilteredObject.Finite.category C ⥤ FilteredObject.Finite.category D :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (FilteredObject D))
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (FilteredObject C)) ⋙
      FilteredObject.mapFunctor F)
    (fun A ↦ map_isFinite F A.property)

/-- Objectwise computation for the functor induced on finite filtered objects. -/
@[simp]
theorem mapFunctor_obj (A : FilteredObject.Finite.category C) :
    ((mapFunctor F).obj A).obj = FilteredObject.map F A.obj := sorry

/-- Morphismwise computation for the functor induced on finite filtered objects. -/
@[simp]
theorem mapFunctor_map {A B : FilteredObject.Finite.category C} (f : A ⟶ B) :
    ((mapFunctor F).map f).hom = Hom.map F f.hom := sorry

end Finite
end Finite

end FilteredObject
end CategoryTheory
