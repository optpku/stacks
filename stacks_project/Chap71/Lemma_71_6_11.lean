module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_6_11_WeaklyAssociated
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Lemma 71.6.11

The pullback of an effective Cartier divisor on an algebraic space is defined
when weakly associated points of the source map outside the divisor, or when
the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.6.11 (1): if every weakly associated point of `X'` maps outside
`D.pointsSet`, then the pullback of the effective Cartier divisor `D` along `f`
is defined. -/
@[stacks 083Z]
theorem pullbackDefined_of_weakAss_outside_support
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (hweak : ∀ x : Points X', x ∈ X'.weakAss → Points.map f x ∉ D.pointsSet) :
    D.pullbackDefined f :=
  sorry

/-- Lemma 71.6.11 (2): the pullback of an effective Cartier divisor along a flat
morphism of algebraic spaces is defined. -/
@[stacks 083Z]
theorem pullbackDefined_of_flat
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Flat f]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    D.pullbackDefined f :=
  sorry

/-- The inverse image of an effective Cartier divisor along a flat morphism of
algebraic spaces is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_inverseImage_of_flat
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Flat f]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    IsEffectiveCartierDivisor (D.inverseImage f).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
