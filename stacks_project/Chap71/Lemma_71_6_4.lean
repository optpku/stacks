/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Complements of effective Cartier divisors

The open complement of an effective Cartier divisor on an algebraic space is
an affine morphism into the ambient space, and is scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor

/-- Lemma 71.6.4 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `i : D ⟶ X` is an effective Cartier divisor, then the open complement
inclusion `closedImmersionComplementι i : closedImmersionComplement i ⟶ X` is
an affine morphism of algebraic spaces. -/
@[stacks 083S]
instance affine_closedImmersionComplementι {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    Affine (closedImmersionComplementι i) :=
  sorry

/-- Lemma 71.6.4 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `i : D ⟶ X` is an effective Cartier divisor, then the open complement
inclusion `closedImmersionComplementι i` is scheme-theoretically dense in `X`. -/
@[stacks 083S]
instance schemeTheoreticallyDense_closedImmersionComplementι
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] :
    IsSchemeTheoreticallyDense (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor
