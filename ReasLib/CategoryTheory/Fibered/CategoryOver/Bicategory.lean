/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- `CategoryTheory.Bicategory.LocallyInduced.Lift` is public because the exported owner is the
-- `Bicategory.LocallyInducedBicategory` and its hom property.
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Property
public import ReasLib.CategoryTheory.Fibered.CategoryOver.ObjectProperty
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The bicategory of fibred categories over a base

`FiberedCategoryOver C` is the locally induced bicategory whose objects have fibred projection
and whose `1`-morphisms preserve strongly cartesian arrows. All vertical based natural
transformations remain available as `2`-morphisms.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w vS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-
`Bicategory.LocallyInducedBicategory` is exactly the required owner: the carrier selects based
categories with fibred projection, its hom property selects the strongly-cartesian-preserving
based functors, and every ambient based natural transformation is retained as a `2`-morphism.
It introduces no redundant wide-subcategory layer for unrestricted `2`-morphisms.

The owner does not choose cleavages. Accordingly, the indexed-category construction
stays with the explicit-cleavage owner `Functor.Cleavage.toPseudofunctor`, and comparison maps
stay with `CartesianBasedFunctor.Reindex.mapIso`; there is no pseudofunctor from raw
`FiberedCategoryOver C` obtained by silently applying choice.
-/

namespace FiberedCategoryOver

/-- The hom property selecting based functors that preserve strongly cartesian morphisms. It is
indexed by the already selected fibred objects, so the object and `1`-morphism restrictions remain
separate reusable layers. -/
abbrev homProperty (C : Type u) [Category.{v} C] :
    Bicategory.HomProperty
      (fun X : (BasedCategory.isFibered.{u, v, w, vS} C).FullSubbicategory ↦ X.1) :=
  fun _ _ ↦ BasedFunctor.PreservesStronglyCartesian

/-- The strongly-cartesian-preserving hom property for fibred categories is multiplicative. -/
instance homProperty.isMultiplicative (C : Type u) [Category.{v} C] :
    (homProperty C).IsMultiplicative where
  id_mem := fun _ {_ _} φ hφ ↦ hφ
  comp_mem := fun {_ _ _} {F G} hF hG {_ _} φ hφ ↦
    hG (F.map φ) (hF φ hφ)

/-- The strongly-cartesian-preserving hom property is invariant under isomorphisms of based
functors, uniformly in its selected fibred source and target. -/
instance homProperty.isClosedUnderIsomorphisms (C : Type u) [Category.{v} C] :
    (homProperty C).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: unfold `homProperty` and apply
`BasedFunctor.PreservesStronglyCartesian.isClosedUnderIsomorphisms` pointwise. -/

end FiberedCategoryOver

set_option linter.checkUnivs false in
/-- `FiberedCategoryOver C` is the locally induced bicategory of based
categories with fibred projection, strongly-cartesian-preserving `1`-morphisms, and all ambient
vertical based natural transformations as `2`-morphisms.

The object and hom universes of the total categories are intentionally independent even though
the carrier sort of the bundled bicategory only records their maximum. -/
@[stacks 02XP "2-category of fibred categories over the base"]
abbrev FiberedCategoryOver (C : Type u) [Category.{v} C] :=
  Bicategory.LocallyInducedBicategory
    (BasedCategory.{vS, w} C)
    (fun X : (BasedCategory.isFibered.{u, v, w, vS} C).FullSubbicategory ↦ X.1)
    (FiberedCategoryOver.homProperty.{u, v, w, vS} C)

namespace FiberedCategoryOver

/-- Forget a fibred category over `C` to its canonical based category. -/
abbrev toBasedCategory (X : FiberedCategoryOver C) : BasedCategory.{vS, w} C :=
  X.1

/-- The total category of a fibred category over `C`. -/
abbrev total (X : FiberedCategoryOver C) :=
  X.toBasedCategory.obj

/-- The projection functor to the base category. -/
abbrev p (X : FiberedCategoryOver C) :=
  X.toBasedCategory.p

/-- Coerce a fibred category over `C` to its underlying based category. -/
instance coeBasedCategory : CoeOut (FiberedCategoryOver C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

variable (C) in
/-- Forget only the cartesian-preservation witness on `1`-morphisms, retaining the selected
fibred objects. -/
abbrev toObject : StrictPseudofunctor (FiberedCategoryOver C)
    (BasedCategory.isFibered.{u, v, w, vS} C).FullSubbicategory :=
  Bicategory.LocallyInducedBicategory.ι (BasedCategory.{vS, w} C)
    (fun X : (BasedCategory.isFibered.{u, v, w, vS} C).FullSubbicategory ↦ X.1)
    (FiberedCategoryOver.homProperty.{u, v, w, vS} C)

variable (C) in
/-- The canonical inclusion of fibred categories over `C` into based categories over `C`.
It remains reducible so the canonical local-fullness and object-property instances stay visible. -/
abbrev toBased : StrictPseudofunctor (FiberedCategoryOver C) (BasedCategory.{vS, w} C) :=
  Bicategory.LocallyInducedBicategory.forget (BasedCategory.{vS, w} C)
    (fun X : (BasedCategory.isFibered.{u, v, w, vS} C).FullSubbicategory ↦ X.1)
    (FiberedCategoryOver.homProperty.{u, v, w, vS} C)

/-- The projection of an object of `FiberedCategoryOver C` is fibred. -/
instance projectionIsFibered (X : FiberedCategoryOver C) : X.p.IsFibered := X.property

/-
`BasedCategory.ofFunctor` may select a category instance not definitionally identical to the
ambient one on `S`. Storing that ambient instance explicitly keeps the supplied `p.IsFibered`
witness well typed while representing exactly the same functor and no additional data.
-/

/-- Build a fibred category over `C` from a fibred functor to `C`. -/
def ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [h : p.IsFibered] :
    FiberedCategoryOver C :=
  ⟨({ obj := S, category := inferInstance, p := p } : BasedCategory C), h⟩

/-- The canonical projection of `ofFunctor p` is the supplied functor `p`. -/
@[simp]
theorem ofFunctor.p {S : Type w} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    (ofFunctor p).p = p := sorry
/- Proof strategy: unfold `ofFunctor`, `FiberedCategoryOver.p`, and `toBasedCategory`; the
stored projection field is definitionally `p`. -/

end FiberedCategoryOver

end CategoryTheory
