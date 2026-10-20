/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.OnSpace
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Equivalence

/-!
# Characterizations of monomorphisms of algebraic stacks

A morphism of algebraic stacks is a monomorphism if and only if it is fully
faithful, if and only if its relative diagonal is an equivalence, if and only
if it becomes a monomorphism of algebraic spaces after one surjective, flat,
locally of finite presentation algebraic-space covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Mono

/-- A morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if `toBasedFunctor f` is fully faithful. -/
theorem iff_fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔ Nonempty (toBasedFunctor f).FullyFaithful :=
  sorry

/-- A monomorphism of algebraic stacks is fully faithful. -/
theorem fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Mono f] :
    Nonempty (toBasedFunctor f).FullyFaithful :=
  (iff_fullyFaithful f).mp inferInstance

/-- A fully faithful morphism of algebraic stacks is a monomorphism. -/
theorem of_fullyFaithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : Nonempty (toBasedFunctor f).FullyFaithful) : Mono f :=
  (iff_fullyFaithful f).mpr hf

/-- A morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if `toBasedFunctor (Hom.diagonal f)` is an
equivalence over the base. -/
theorem iff_diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (iff_fullyFaithful f).trans
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.fullyFaithful_iff_isEquivalence f)

/-- The relative diagonal of a monomorphism of algebraic stacks is an
equivalence over the base. -/
instance diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Mono f] :
    BasedFunctor.IsEquivalence
      (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  (iff_diagonal_isEquivalence f).mp inferInstance

/-- If the relative diagonal of a morphism of algebraic stacks is an
equivalence over the base, then the morphism is a monomorphism. -/
theorem of_diagonal_isEquivalence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : BasedFunctor.IsEquivalence
      (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1} f))) :
    Mono f :=
  (iff_diagonal_isEquivalence f).mpr h

/-- A morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if and only if there exist an algebraic space `W` and a
surjective, flat, locally of finite presentation morphism
`g : W.toGroupoids ⟶ Y` together with a representing morphism of algebraic
spaces `v : V ⟶ W` for the projection of `X ×_Y W` that is a monomorphism. -/
theorem iff_exists_covering_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Mono f ↔
      ∃ (W : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y),
        Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
          ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
            RepresentsTwoFibreProductOnSpace f g V W v ∧
              CategoryTheory.Mono v :=
  sorry

/-- If a morphism of algebraic stacks becomes a monomorphism of algebraic
spaces after one surjective, flat, locally of finite presentation
algebraic-space covering, then it is a monomorphism. -/
theorem of_exists_covering_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∃ (W : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y),
      Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
          RepresentsTwoFibreProductOnSpace f g V W v ∧
            CategoryTheory.Mono v) :
    Mono f :=
  (iff_exists_covering_mono f).mpr h

/-- If `f : X ⟶ Y` is a morphism of algebraic stacks and `g : Z ⟶ Y` is a
monomorphism, then the canonical projection `Z ×_Y X ⟶ X` is a monomorphism. -/
@[instance]
theorem pullback_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Mono g] :
    Mono (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f) :=
  sorry

end Mono

end AlgebraicGeometry.Groupoids.Hom
