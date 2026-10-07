module

public import stacks_project.Chap10.Lemma_10_127_10
public import stacks_project.Chap10.Lemma_10_127_11_Pre
import StacksCheckRecall

/-!
# Two approximation systems for the same local map

@stack 00QW
-/

@[expose] public section

universe u v

/-- **Remark 10.127.12** ([Stacks tag 00QW](https://stacks.math.columbia.edu/tag/00QW)):
some local essentially finitely presented map admits both an approximation system whose
transitions are localizations at prime ideals and another system whose transitions are
localizations of quotients but not all localizations at prime ideals. -/
@[stacks 00QW]
theorem exists_essentially_finitePresentation_local_map_with_wrong_approximation_system :
    ∃ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S) (_ : IsLocalRing R)
      (_ : IsLocalRing S) (f : R →+* S) (_ : IsLocalHom f)
      (_ : RingHom.EssFinitePresentation f) (goodSystem : DirectedLocalHomApproximation f),
      goodSystem.HasPrimeLocalizationTransitions ∧
        ∃ badSystem : DirectedLocalHomApproximation f,
          badSystem.HasLocalizationOfQuotientTransitions ∧
            badSystem.HasFailingPrimeLocalizationTransition := sorry

@[stacks 00QW "approximation-system owner"]
#check @DirectedLocalHomApproximation

@[stacks 00QW "good transition condition"]
#check @DirectedLocalHomApproximation.HasPrimeLocalizationTransitions

@[stacks 00QW "quotient-localization transition condition"]
#check @DirectedLocalHomApproximation.HasLocalizationOfQuotientTransitions

@[stacks 00QW "failing prime-localization transition"]
#check @DirectedLocalHomApproximation.HasFailingPrimeLocalizationTransition
