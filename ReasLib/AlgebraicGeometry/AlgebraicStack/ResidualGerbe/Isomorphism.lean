/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Morphisms inducing isomorphisms of residual gerbes

A morphism induces an isomorphism of residual gerbes at specified points when
it sends one point to the other and admits a commuting equivalence between
residual-gerbe inclusions at those points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks sends `u` to `x` and induces an isomorphism of
residual gerbes at those points: some residual-gerbe inclusions `ιu` at `u` and
`ιx` at `x` admit a 2-commutative comparison 1-morphism whose underlying based
functor is an equivalence. -/
def inducesIsoOnResidualGerbes {S : Scheme.{u}} {U X : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] (f : U ⟶ X) (u : Points U)
    (x : Points X) : Prop :=
  Points.map f u = x ∧
    ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu) (_ : AlgebraicStack Zx)
      (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
      IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
        (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f)

namespace inducesIsoOnResidualGerbes

/-- `inducesIsoOnResidualGerbes f u x` unpacks to `Points.map f u = x` together
with residual-gerbe inclusions at `u` and `x` and a 2-commutative comparison
that is a based-functor equivalence. -/
theorem iff {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X) (u : Points U) (x : Points X) :
    inducesIsoOnResidualGerbes f u x ↔
      Points.map f u = x ∧
        ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu)
          (_ : AlgebraicStack Zx) (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
          IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
            (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f) := sorry

/-- A point-mapping morphism together with residual-gerbe inclusions and a
2-commutative based-functor equivalence between them witnesses
`inducesIsoOnResidualGerbes f u x`. -/
theorem of {S : Scheme.{u}} {U X Zu Zx : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] [AlgebraicStack Zu] [AlgebraicStack Zx] (f : U ⟶ X)
    {u : Points U} {x : Points X} (hu : Points.map f u = x) (ιu : Zu ⟶ U)
    (ιx : Zx ⟶ X) [IsResidualGerbe ιu u] [IsResidualGerbe ιx x] (h : Zu ⟶ Zx)
    (h_equiv : (toBasedFunctor h).IsEquivalence)
    (h_comm : Nonempty (h ≫ ιx ≅ ιu ≫ f)) :
    inducesIsoOnResidualGerbes f u x := sorry

/-- `inducesIsoOnResidualGerbes f u x` supplies `Points.map f u = x` together
with residual-gerbe inclusions at `u` and `x` and a 2-commutative comparison
that is a based-functor equivalence. -/
theorem spec {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] {f : U ⟶ X} {u : Points U} {x : Points X}
    (h : inducesIsoOnResidualGerbes f u x) :
    Points.map f u = x ∧
      ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu)
        (_ : AlgebraicStack Zx) (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
        IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
          (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f) := sorry

end inducesIsoOnResidualGerbes

end AlgebraicGeometry.AlgebraicStack
