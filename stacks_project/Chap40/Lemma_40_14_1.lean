module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

export AlgebraicGeometry.GroupoidScheme
  (sourcePushforwardFittingIdealSheaf_monotone
    sourcePushforwardFittingFiltration
    sourcePushforwardFittingFiltration_apply
    sourcePushforwardFittingZero_eq_bot
    sourcePushforwardFittingFiltration_zero
    sourcePushforwardPullbacks_isIsomorphic
    sourcePushforwardFittingIdealSheaf_comap_target_eq_comap_source
    sourcePushforwardFittingFiltration_isClosedInvariant
    iInter_support_sourcePushforwardFittingFiltration_eq_empty
    sourcePushforwardRankStratum_isFiniteLocallyFreeOfRank
    sourcePushforwardFittingFiltration_rankStratum
    exists_invariantRankStratification)

end AlgebraicGeometry.Scheme.Groupoid

/- Lemma 40.14.1: a groupoid scheme with finite source and target maps admits an invariant
closed filtration beginning with the whole object scheme, with empty total intersection, and
with source pullback finite locally free of rank `r + 1` on the difference of stages `r`
and `r + 1`. -/
@[stacks 0AB9] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantRankStratification :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [IsFinite G.s.left] [IsFinite G.t.left],
      ∃ Z : ℕ →o Scheme.IdealSheafData G.U.left,
        Z 0 = ⊥ ∧
        (∀ r, G.toPreRelation.IsClosedInvariant (Z r)) ∧
        (⋂ r, ((Z r).support : Set G.U.left)) = (∅ : Set G.U.left) ∧
        ∀ r, IsFiniteLocallyFreeOfRank
        (pullback.snd G.s.left
          (((Z (r + 1)).comap (Z r).subschemeι).openComplement.ι ≫
            (Z r).subschemeι))
        (r + 1))
