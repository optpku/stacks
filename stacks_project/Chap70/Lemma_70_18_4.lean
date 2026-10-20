module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.StalkGluing.FiniteFamily

universe u

/- Lemma 70.18.4. For finitely many pairwise distinct closed points with
quasi-compact open complement, canonical base change gives the equivalence of
finite-presentation algebraic-space categories. For each point, the pulled-back
open `(S.fromSpecStalk (s i)) ⁻¹ᵁ U` is the punctured local spectrum, by
`AlgebraicGeometry.Scheme.preimage_fromSpecStalk_eq_puncturedOpen_of_compl_range`. -/
@[stacks 0E92] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.stalkGlueFamilyFunctor_isEquivalence :
    ∀ {ι : Type} [Finite ι] {S : AlgebraicGeometry.Scheme.{u}}
      (U : S.Opens) [AlgebraicGeometry.QuasiCompact U.ι] (s : ι → S)
      (hs_closed : ∀ i, s i ∈ closedPoints S) (hs_inj : Function.Injective s)
      (hU : (U : Set S) = (Set.range s)ᶜ),
      (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.stalkGlueFamilyFunctor U s).IsEquivalence)
