/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Product
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.55.6

Stacks 00JH is recalled through the two ReasLib product decompositions: one for finitely
generated projective modules and one for finitely generated modules.

@stack 00JH
-/

/- Lemma 10.55.6 (1): `K₀(R₁ × R₂)` is the product of `K₀(R₁)` and `K₀(R₂)`. -/
@[stacks 00JH "finite-projective K0 product decomposition"]
#check @CategoryTheory.ModuleCat.K0.Product.Projective.equiv

/- Lemma 10.55.6 (2): `K₀'(R₁ × R₂)` is the product of `K₀'(R₁)` and `K₀'(R₂)`. -/
@[stacks 00JH "finite-module K0 product decomposition"]
#check @CategoryTheory.ModuleCat.K0.Product.Finite.equiv
