module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Lemma_100_4_3_Comparison

/-!
# Universally injective morphisms of algebraic stacks

A morphism of algebraic stacks is universally injective when every
2-fibre-product base change induces an injective map on underlying point
spaces.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is universally injective if every
2-fibre-product base change induces an injective map on underlying point
spaces. -/
@[mk_iff]
class UniversallyInjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` induces an injective map on
  points. -/
  injective_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z]
      [AlgebraicStack P] {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
      (iso : fst ≫ f ≅ snd ≫ g) :
      (Points.cone iso).IsBilimit → Function.Injective (Points.map snd)

namespace UniversallyInjective

/-- The identity morphism of an algebraic stack is universally injective. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallyInjective (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is universally injective. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    UniversallyInjective f :=
  sorry

/-- A universally injective morphism has injective 2-fibre-product base
changes on points. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyInjective f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : Function.Injective (Points.map snd) :=
  sorry

/-- A morphism is universally injective as soon as every 2-fibre-product base
change induces an injective map on points. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g),
      (Points.cone iso).IsBilimit → Function.Injective (Points.map snd)) :
    UniversallyInjective f :=
  sorry

/-- A universally injective morphism induces an injective map on points. -/
theorem map_injective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    [UniversallyInjective f] : Function.Injective (Points.map f) :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally
injective morphism `f : X ⟶ Y` induces an injective map on points, once the
apex is known to be an algebraic stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyInjective f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Function.Injective
      (Points.map (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  sorry

end UniversallyInjective

/-- A morphism of algebraic stacks is universally injective if and only if
every 2-fibre-product base change, expressed by an `IsBilimit` square,
induces an injective map on points. -/
theorem universallyInjective_iff_injective_of_isBilimit {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyInjective f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → Function.Injective (Points.map snd) :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` induces an injective
map on points. -/
theorem universallyInjective_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyInjective f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        Function.Injective
          (Points.map (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
