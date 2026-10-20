module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.Excision

/-! # Excision for modifications of algebraic spaces -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.19.1: let `S` be a scheme and `f : V ⟶ W` a separated étale
morphism of algebraic spaces over `S`. If `i : T ⟶ W` is a closed immersion
such that `inverseImageTo f i : f⁻¹T ⟶ T` is an isomorphism, then with
`W⁰ = closedImmersionComplement i` and
`V⁰ = openInverseImage f (closedImmersionComplementι i)`, the base-change
functor `IsoOverOpen.baseChange f (closedImmersionComplementι i)` from
morphisms `g : X ⟶ W` that are isomorphisms over `W⁰` to morphisms
`h : Y ⟶ V` that are isomorphisms over `V⁰` is an equivalence of
categories. -/
@[stacks 0BGY] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.baseChange_isEquivalence :
  ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)],
    (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.baseChange f
      (closedImmersionComplementι i)).IsEquivalence)
