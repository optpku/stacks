/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Right
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

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
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Function.Injective (Points.map snd)

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
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Function.Injective (Points.map snd) :=
  UniversallyInjective.injective_baseChange iso h

/-- A morphism is universally injective as soon as every 2-fibre-product base
change induces an injective map on points. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g),
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Function.Injective (Points.map snd)) :
    UniversallyInjective f :=
  ⟨hf⟩

/-- A universally injective morphism induces an injective map on points. -/
theorem map_injective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    [UniversallyInjective f] : Function.Injective (Points.map f) :=
  by
    let c := CategoryTheory.Bicategory.PseudoPullbackCone.ofRightEquivalence f
      (CategoryTheory.Bicategory.Equivalence.OnHom.id Y)
    have hc : c.IsBilimit :=
      CategoryTheory.Bicategory.PseudoPullbackCone.ofRightEquivalence.isBilimit f _
    have h : Function.Injective (Points.map (f ≫ 𝟙 Y)) :=
      UniversallyInjective.spec c.iso hc
    have hm : Points.map (f ≫ 𝟙 Y) = Points.map f := by
      funext x
      simp only [Points.map_comp, Points.map_id]
    rw [← hm]
    exact h

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally
injective morphism `f : X ⟶ Y` induces an injective map on points, once the
apex is known to be an algebraic stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyInjective f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Function.Injective
      (Points.map (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  UniversallyInjective.spec (TwoFibreProduct.comparisonIso f g)
    (TwoFibreProduct.cone.isBilimit f g)

end UniversallyInjective

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
  by
    constructor
    · intro hf
      letI : UniversallyInjective f := hf
      intro Z _ g _
      exact UniversallyInjective.twoFibreProduct_snd g
    · sorry

end AlgebraicGeometry.AlgebraicStack
