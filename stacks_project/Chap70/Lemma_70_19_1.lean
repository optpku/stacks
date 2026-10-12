/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange

/-!
# Excision for modifications of algebraic spaces

A separated étale morphism that is an isomorphism over a closed subspace
induces an equivalence of iso-over-open slice categories on the complementary
opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverOpen

/-- Lemma 70.19.1: let `S` be a scheme and `f : V ⟶ W` a separated étale
morphism of algebraic spaces over `S`. If `i : T ⟶ W` is a closed immersion
such that `inverseImageTo f i : f⁻¹T ⟶ T` is an isomorphism, then with
`W⁰ = closedImmersionComplement i` and
`V⁰ = openInverseImage f (closedImmersionComplementι i)`, the base-change
functor `IsoOverOpen.baseChange f (closedImmersionComplementι i)` from
morphisms `g : X ⟶ W` that are isomorphisms over `W⁰` to morphisms
`h : Y ⟶ V` that are isomorphisms over `V⁰` is an equivalence of
categories. -/
@[stacks 0BGY, instance]
instance baseChange_isEquivalence {S : Scheme.{u}}
    {V W T : AlgebraicSpace S} (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)] :
    (baseChange f (closedImmersionComplementι i)).IsEquivalence :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
