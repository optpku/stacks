module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Effective Cartier divisors drop local dimension

An effective Cartier divisor on an algebraic space has strictly smaller local
dimension at every point of finite local dimension on the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.6.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `i : D ⟶ X` be an effective Cartier divisor. Let `x` be a point of `|D|`.
If `dimensionAt (Points.map i x) < ⊤`, then
`dimensionAt x < dimensionAt (Points.map i x)`. -/
@[stacks 083T]
theorem IsEffectiveCartierDivisor.dimensionAt_lt
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] (x : |D|)
    (hfin : dimensionAt (Points.map i x) < ⊤) :
    dimensionAt x < dimensionAt (Points.map i x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
