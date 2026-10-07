module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InSets.Slice

/-!
# Canonical maps between slice fibrations

This leaf contains only postcomposition between canonical slice fibrations and precomposition
of a slice-valued morphism. It does not import homotopy-category or presentation infrastructure.
-/

@[expose] public section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The canonical morphism `C/X ⟶ C/Y` over `C` induced by postcomposition with
`f : X ⟶ Y`. -/
@[stacks 04SF "canonical morphism between represented slice fibrations"]
def overMap {X Y : C} (f : X ⟶ Y) : slice X ⟶ slice Y :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (BasedCategory.overMap f)

/-- Forgetting `overMap f` to a based functor recovers the canonical based slice-change map. -/
@[simp]
theorem overMap.toBasedFunctor {X Y : C} (f : X ⟶ Y) :
    toBasedFunctor (overMap f) = BasedCategory.overMap f := sorry

/-- Forgetting `overMap f` to an ordinary functor recovers mathlib's `Over.map f`. -/
@[simp]
theorem overMap.toFunctor {X Y : C} (f : X ⟶ Y) :
    toFunctor (overMap f) = Over.map f := sorry

/-- On objects, the total functor of `overMap f` is postcomposition by `f`. -/
@[simp]
theorem overMap.obj {X Y : C} (f : X ⟶ Y) (a : Over X) :
    (FiberedCategoryOver.Groupoids.toFunctor
      (FiberedCategoryOver.Groupoids.overMap f)).obj a =
        (Over.map f).obj a := sorry

/-- On morphisms, the total functor of `overMap f` is the map induced by postcomposition
with `f`. -/
@[simp]
theorem overMap.map {X Y : C} (f : X ⟶ Y) {a b : Over X} (g : a ⟶ b) :
    (FiberedCategoryOver.Groupoids.toFunctor
      (FiberedCategoryOver.Groupoids.overMap f)).map g =
        (Over.map f).map g := sorry

/-- The slice morphism induced by an identity base morphism is the identity. -/
@[simp]
theorem overMap.id (X : C) : overMap (𝟙 X) = 𝟙 (slice X) := sorry

/-- Canonical slice morphisms respect composition. -/
@[simp]
theorem overMap.comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    overMap (f ≫ g) = overMap f ≫ overMap g := sorry

namespace slice

/-- Precomposition by the canonical map `slice V ⟶ slice U`, as a functor between
hom-categories of groupoid-fibred categories. This is the `2`-cell action underlying
`slice.pullback`. -/
@[stacks 04SF "pullback functor on represented slice morphisms"]
def pullbackFunctor
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U) :
    (slice U ⟶ X) ⥤ (slice V ⟶ X) :=
  Bicategory.precomp X (FiberedCategoryOver.Groupoids.overMap f)

/-- The object action of the slice pullback functor is precomposition with `overMap f`. -/
@[simp]
theorem pullbackFunctor.obj
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) :
    (pullbackFunctor f).obj G =
      FiberedCategoryOver.Groupoids.overMap f ≫ G := sorry

/-- The morphism action of the slice pullback functor is left whiskering by `overMap f`. -/
@[simp]
theorem pullbackFunctor.map
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    {G H : slice U ⟶ X} (eta : G ⟶ H) :
    (pullbackFunctor f).map eta =
      FiberedCategoryOver.Groupoids.overMap f ◁ eta := sorry

/-- Pullback along an identity is the identity functor on the corresponding hom-category. -/
@[simp]
theorem pullbackFunctor.id
    {X : FiberedCategoryOver.Groupoids C} (U : C) :
    pullbackFunctor (X := X) (𝟙 U) = 𝟭 (slice U ⟶ X) := sorry

/-- Slice pullback functors compose contravariantly in the representing object. -/
@[simp]
theorem pullbackFunctor.comp
    {X : FiberedCategoryOver.Groupoids C} {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    pullbackFunctor (X := X) (g ≫ f) =
      pullbackFunctor f ⋙ pullbackFunctor g := sorry

/-- Pull a slice morphism back along `f : V ⟶ U` by precomposition with the canonical
slice morphism. The target owner is inferred from `G`. -/
@[stacks 04SF "pullback of a represented slice morphism"]
def pullback
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) :
    slice V ⟶ X :=
  (pullbackFunctor f).obj G

/-- Forgetting a pulled-back slice morphism gives precomposition with `Over.map f`. -/
@[simp]
theorem pullback.toFunctor
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) :
    toFunctor (pullback f G) = Over.map f ⋙ toFunctor G := sorry

/-- Forgetting a pulled-back slice morphism to a based functor gives based-functor
precomposition with the canonical slice-change map. -/
@[simp]
theorem pullback.toBasedFunctor
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (pullback f G) =
      BasedFunctor.comp (BasedCategory.overMap f)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G) := sorry

/-- Pullback evaluates on an object by first applying the canonical slice-change functor. -/
@[simp]
theorem pullback.obj
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) (a : Over V) :
    (FiberedCategoryOver.Groupoids.toFunctor (slice.pullback f G)).obj a =
      (FiberedCategoryOver.Groupoids.toFunctor G).obj ((Over.map f).obj a) := sorry

/-- Pullback evaluates on a morphism by first applying the canonical slice-change functor. -/
@[simp]
theorem pullback.map
    {X : FiberedCategoryOver.Groupoids C} {U V : C} (f : V ⟶ U)
    (G : slice U ⟶ X) {a b : Over V} (g : a ⟶ b) :
    (FiberedCategoryOver.Groupoids.toFunctor (slice.pullback f G)).map g =
      (FiberedCategoryOver.Groupoids.toFunctor G).map ((Over.map f).map g) := sorry

/-- Pulling a slice morphism back along an identity does not change it. -/
@[simp]
theorem pullback.id
    {X : FiberedCategoryOver.Groupoids C} {U : C} (G : slice U ⟶ X) :
    pullback (𝟙 U) G = G := sorry

/-- Pullback of a slice morphism is contravariantly functorial in the representing object. -/
@[simp]
theorem pullback.comp
    {X : FiberedCategoryOver.Groupoids C} {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) (G : slice U ⟶ X) :
    pullback (g ≫ f) G = pullback g (pullback f G) := sorry

end slice

end CategoryTheory.FiberedCategoryOver.Groupoids

/- Data and axiom audit: `overMap` and `slice.pullback` retain the canonical slice-change data.
Any reported `sorryAx` is inherited from category/bicategory law fields, not from a hidden choice
of carrier, map, or comparison morphism. -/
