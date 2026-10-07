module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Counterexample

@[expose] public section

universe u

/- Lemma 110.18.1: there exists a local Noetherian 2-dimensional domain `B`, complete
with respect to a principal ideal `I = Ideal.span {b}`, and an element `f` of the
maximal ideal not in `I`, such that the `I`-adic completion `C` of
`Localization.Away f` is nonreduced and even `C[1/b]` is nonreduced. -/
@[stacks 0GHI] #check
(AdicCompletion.Counterexample.exists_nonreduced_localization :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B) (b f : B),
      ringKrullDim B = 2 ∧ IsAdicComplete (Ideal.span {b}) B ∧
        f ∈ IsLocalRing.maximalIdeal B ∧ f ∉ Ideal.span {b} ∧
        ¬ IsReduced
          (AdicCompletion (Ideal.map (algebraMap B (Localization.Away f)) (Ideal.span {b}))
            (Localization.Away f)) ∧
        ¬ IsReduced
          (Localization.Away
            (algebraMap B
              (AdicCompletion (Ideal.map (algebraMap B (Localization.Away f)) (Ideal.span {b}))
                (Localization.Away f)) b)))
