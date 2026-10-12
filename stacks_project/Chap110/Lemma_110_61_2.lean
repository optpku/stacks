/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.CoproductToProduct
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Coproducts of shifted locally quasi-coherent modules agree with products
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open Limits

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The object of `D(𝒪_X)` obtained by placing `F n` in cohomological degree
`-n`, matching the Stacks shift `F n[n]`. -/
noncomputable abbrev shiftSingle {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : ℕ → fppfModules X) (n : ℕ) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (fppfModules X) (-(n : ℤ))).obj (F n)

/-- Each shifted sheaf `F n[n]` has cohomology in `LQCoh^{fbc}`. -/
theorem cohomologyIn_shiftSingle {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (F : ℕ → fppfModules X) (n : ℕ)
    (hF : FppfModules.lqcohFbc X (F n)) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) (shiftSingle F n) :=
  sorry

/-- The coproduct of the shifted family `n ↦ F n[n]` has cohomology in
`LQCoh^{fbc}`. -/
theorem cohomologyIn_coproduct_shiftSingle {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (F : ℕ → fppfModules X)
    (hF : ∀ n, FppfModules.lqcohFbc X (F n))
    [HasCoproductsOfShape ℕ (ModuleDerived X)] :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) (∐ shiftSingle F) :=
  sorry

/-- Lemma 110.61.2: if `X` is an algebraic stack and `F n` is a collection of
locally quasi-coherent sheaves with the flat base change property on `X`, then
the canonical map `∐ shiftSingle F ⟶ ∏ᶜ shiftSingle F` is an isomorphism in
`D(𝒪_X)`. -/
@[stacks 08IZ]
theorem shiftSingle_coproductToProduct_isIso {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (F : ℕ → fppfModules X)
    (hF : ∀ n, FppfModules.lqcohFbc X (F n))
    [HasCoproductsOfShape ℕ (ModuleDerived X)]
    [HasProductsOfShape ℕ (ModuleDerived X)] :
    IsIso (coproductToProduct (shiftSingle F)) := sorry

end AlgebraicGeometry.AlgebraicStack
