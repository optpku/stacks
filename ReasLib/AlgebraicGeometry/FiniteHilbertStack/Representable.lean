/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Representability of morphisms of finite Hilbert stacks

A morphism representable by algebraic spaces induces a morphism of finite
Hilbert stacks representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X' X Y : GroupoidsOver S}
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]

/-- A morphism `G : X' ⟶ X` of stacks in groupoids over `(Sch/S)_fppf`
representable by algebraic spaces induces a morphism
`H_d(X'/Y) ⟶ H_d(X/Y)` representable by algebraic spaces. -/
@[stacks 05YJ]
theorem map.relativelyRepresentableByAlgebraicSpaces
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ)
    (hG : relativelyRepresentableByAlgebraicSpaces G) :
    relativelyRepresentableByAlgebraicSpaces (map G F d) := sorry

/-- The 2-fibre product `(Sch/U)_fppf ×_ξ H_d(X'/Y)` along a Yoneda test
`ξ` of `H_d(X/Y)` is represented by an algebraic space over `U` when
`G : X' ⟶ X` is representable by algebraic spaces. -/
theorem twoFibreProduct.represents (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ)
    (hG : relativelyRepresentableByAlgebraicSpaces G) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) :
    ∃ (W : AlgebraicSpace S) (fW : W ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange (map G F d) (YonedaSlice.representative ξ) W fW :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
