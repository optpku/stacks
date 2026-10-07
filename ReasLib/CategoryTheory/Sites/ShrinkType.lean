module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.Logic.Small.Basic

/-!
# Universe-shrinking for type-valued sheaves

This file owns the concrete `Shrink` model of a universe of types and its
interaction with local properties of presheaf morphisms.  It is intentionally
independent of any particular Chapter 7 argument.
-/

@[expose] public section

open CategoryTheory

universe t w u v

namespace CategoryTheory.Sites

/-- Transport a morphism of `Type t` through the `Shrink.{w}` equivalences. -/
@[implicit_reducible]
noncomputable def typeShrinkMap
    [UnivLE.{t, w}] {X Y : Type t} (f : X ⟶ Y) :
    Shrink.{w} X → Shrink.{w} Y :=
  fun x => equivShrink Y (f ((equivShrink X).symm x))

/-- `typeShrinkMap` sends identity maps to identity functions. -/
theorem typeShrinkMap_id
    [UnivLE.{t, w}] (X : Type t) :
    typeShrinkMap (𝟙 X) = id := sorry

/-- `typeShrinkMap` respects composition. -/
theorem typeShrinkMap_comp
    [UnivLE.{t, w}] {X Y Z : Type t} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typeShrinkMap (f ≫ g) = typeShrinkMap g ∘ typeShrinkMap f := sorry

/-- The hom type used to view `Type t` concretely in the smaller universe
`Type w`. -/
@[implicit_reducible]
noncomputable def shrinkHom
    [UnivLE.{t, w}] (X Y : Type t) : Type w :=
  Shrink.{w} X → Shrink.{w} Y

/-- Shrink-carrier morphisms are function-like. -/
instance shrinkHomFunLike [UnivLE.{t, w}] (X Y : Type t) :
    FunLike (shrinkHom.{t, w} X Y) (Shrink.{w} X) (Shrink.{w} Y) where
  coe f := f
  coe_injective := sorry

/-- Convert a morphism of shrink carriers back to a map of the original types. -/
@[implicit_reducible]
noncomputable def shrinkHomToFunction
    [UnivLE.{t, w}] {X Y : Type t} (f : shrinkHom.{t, w} X Y) : X ⟶ Y :=
  TypeCat.ofHom fun x => (equivShrink Y).symm (f (equivShrink X x))

/-- Shrinking after converting a shrink-carrier map back to a type map is the
original map. -/
theorem typeShrinkMap_shrinkHomToFunction
    [UnivLE.{t, w}] {X Y : Type t} (f : shrinkHom.{t, w} X Y) :
    typeShrinkMap (shrinkHomToFunction f) = f := sorry

/-- Converting a shrunk type map back to an ordinary map recovers the original
morphism. -/
theorem shrinkHomToFunction_typeShrinkMap
    [UnivLE.{t, w}] {X Y : Type t} (f : X ⟶ Y) :
    shrinkHomToFunction (typeShrinkMap f) = f := sorry

/-- The `Shrink` carrier realizes `Type t` as a concrete category over
`Type w`. -/
@[implicit_reducible]
noncomputable def shrinkConcreteCategory [UnivLE.{t, w}] :
    ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) where
  hom f := typeShrinkMap f
  ofHom f := shrinkHomToFunction f
  hom_ofHom := sorry
  ofHom_hom := sorry
  id_apply := sorry
  comp_apply := sorry

/-- The canonical forgetful functor from `Type t` to the shrink carriers in
`Type w`.  The local concrete-category instance is a definitional pin for this
specific functor and is not exported as a global instance. -/
@[implicit_reducible]
noncomputable def shrinkForget [UnivLE.{t, w}] :
    Type t ⥤ Type w :=
  letI : ConcreteCategory.{w} (Type t) (shrinkHom.{t, w}) := shrinkConcreteCategory
  CategoryTheory.forget (Type t)

/-- `shrinkForget` maps a morphism by `typeShrinkMap`. -/
theorem shrinkForget_map_apply [UnivLE.{t, w}] {X Y : Type t}
    (f : X ⟶ Y) (x : Shrink.{w} X) :
    (shrinkForget.{t, w}).map f x = typeShrinkMap f x := sorry

/-- The shrink-carrier forgetful functor reflects isomorphisms. -/
instance shrinkForget_reflectsIsomorphisms [UnivLE.{t, w}] :
    (shrinkForget.{t, w}).ReflectsIsomorphisms := sorry

/-- A sheaf of `Type t`-valued presheaves remains a sheaf after shrinking its
values into `Type w`. -/
theorem shrinkForget_isSheaf
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type t}
    (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ shrinkForget.{t, w}) := sorry

/-- Composition with `shrinkForget` preserves the sheaf condition. -/
instance shrinkForget_hasSheafCompose
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (shrinkForget.{t, w}) := sorry

/-- Local injectivity is preserved after whiskering with `shrinkForget`. -/
theorem isLocallyInjective_whisker_shrinkForget
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q)
    (h_f : Presheaf.IsLocallyInjective J f) :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f (shrinkForget.{t, w})) := sorry

/-- Local surjectivity is preserved after whiskering with `shrinkForget`. -/
theorem isLocallySurjective_whisker_shrinkForget
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q)
    (h_f : Presheaf.IsLocallySurjective J f) :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f (shrinkForget.{t, w})) := sorry

/-- Local injectivity of a type-valued presheaf map follows from local
injectivity after shrinking its values. -/
theorem locallyInjective_of_shrink
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q)
    (h_f : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f (shrinkForget.{t, w}))) :
    Presheaf.IsLocallyInjective J f := sorry

/-- Local surjectivity of a type-valued presheaf map follows from local
surjectivity after shrinking its values. -/
theorem locallySurjective_of_shrink
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q)
    (h_f : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f (shrinkForget.{t, w}))) :
    Presheaf.IsLocallySurjective J f := sorry

/-- If weak equivalences are locally bijective in both type universes, then
`shrinkForget` preserves sheafification. -/
instance shrinkForget_preservesSheafification_of_WEqualsLocallyBijective
    [UnivLE.{t, w}] {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type t)] [HasWeakSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type t)] [J.WEqualsLocallyBijective (Type w)] :
    J.PreservesSheafification (shrinkForget.{t, w}) := sorry

end CategoryTheory.Sites
