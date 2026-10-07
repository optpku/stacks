module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_36_6_Comparison

/-!
# Characterizations of unramified morphisms of algebraic stacks

A morphism of algebraic stacks is unramified if and only if it is DM and every
étale algebraic-space test of a 2-fibre product against an algebraic space over
the target is unramified, and if and only if some fppf algebraic-space cover of
the target has a surjective étale unramified algebraic-space test of the
2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- Lemma 101.36.6: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `f` is unramified; `f` is DM and for every algebraic
space `V` with `g : V.toGroupoids ⟶ Y` and every étale morphism from an
algebraic space into `TwoFibreProduct.apex f g`, the recovered morphism of
algebraic spaces is unramified; there exist a surjective, flat, locally of
finite presentation morphism from an algebraic space `W` to `Y` and a
surjective étale morphism from an algebraic space `T` to
`TwoFibreProduct.apex f g` such that the recovered morphism `T ⟶ W` is
unramified. -/
@[stacks 0CIY]
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Unramified f, DM f ∧ forallEtaleOnPullbacks f, existsFppfEtaleSquare f] :=
  sorry

/-- A morphism of algebraic stacks is unramified if and only if it is DM and
every étale algebraic-space comparison into a 2-fibre product against an
algebraic space over the target recovers an unramified morphism. -/
theorem iff_forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔ DM f ∧ forallEtaleOnPullbacks f :=
  sorry

/-- A morphism of algebraic stacks is unramified if and only if some fppf
algebraic-space cover of the target has a surjective étale algebraic-space
comparison into the 2-fibre product whose recovered morphism is unramified. -/
theorem iff_existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔ existsFppfEtaleSquare f :=
  sorry

/-- An unramified morphism of algebraic stacks has unramified recovered
morphisms for every étale algebraic-space comparison into a 2-fibre product
against an algebraic space over the target. -/
theorem forallEtaleOnPullbacks_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    forallEtaleOnPullbacks f :=
  sorry

/-- If a morphism of algebraic stacks is DM and every étale algebraic-space
comparison into a 2-fibre product against an algebraic space over the target
recovers an unramified morphism, then the morphism is unramified. -/
theorem of_forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (hDM : DM f)
    (h : forallEtaleOnPullbacks f) : Unramified f :=
  sorry

/-- An unramified morphism of algebraic stacks admits an fppf algebraic-space
cover of the target together with a surjective étale algebraic-space
comparison into the 2-fibre product whose recovered morphism is unramified. -/
theorem existsFppfEtaleSquare_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    existsFppfEtaleSquare f :=
  sorry

/-- An fppf algebraic-space cover of the target together with a surjective
étale algebraic-space comparison into the 2-fibre product whose recovered
morphism is unramified implies that a morphism of algebraic stacks is
unramified. -/
theorem of_existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : existsFppfEtaleSquare f) : Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
