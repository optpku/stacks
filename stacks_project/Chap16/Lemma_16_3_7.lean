/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Localization

@[expose] public section

universe u v

/- Lemma 16.3.7 (1): standard smoothness after inverting `a` gives smoothness and free Kähler
differentials. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (a : A) [Algebra.IsStandardSmooth R (Localization.Away a)] ↦
  And.intro
    (inferInstance : Algebra.Smooth R (Localization.Away a))
    (inferInstance : Module.Free (Localization.Away a) Ω[Localization.Away a⁄R])

/- Lemma 16.3.7 (2): smoothness together with free Kähler differentials implies smoothness
together with stably free Kähler differentials. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (a : A)
    (h : Algebra.Smooth R (Localization.Away a) ∧
      Module.Free (Localization.Away a) Ω[Localization.Away a⁄R]) ↦
  And.intro h.1 (Module.StablyFree.of_free h.2)

/- Lemma 16.3.7 (3): smoothness together with stably free Kähler differentials implies
smoothness. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (a : A)
    (h : Algebra.Smooth R (Localization.Away a) ∧
      Module.StablyFree (Localization.Away a) Ω[Localization.Away a⁄R]) ↦
  h.1

/- Lemma 16.3.7 (4): every elementary standard element is strictly standard. -/
@[stacks 07EZ] #check @Algebra.IsElementaryStandard.isStrictlyStandard

/- Lemma 16.3.7 (5): an elementary standard element gives a standard-smooth localization. -/
@[stacks 07EZ] #check @Algebra.IsElementaryStandard.isStandardSmoothAway

/- Lemma 16.3.7 (6): a strictly standard element gives a smooth localization with stably free
Kähler differentials. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {a : A} (h : Algebra.IsStrictlyStandard R a) ↦
  And.intro (Algebra.IsStrictlyStandard.smoothAway h)
    (Algebra.IsStrictlyStandard.stablyFree_kaehlerDifferential_away h)

/- Lemma 16.3.7 (7): smoothness and stable freeness after inverting `a` eventually make every
sufficiently large power of `a` strictly standard. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A)
    (h : Algebra.Smooth R (Localization.Away a) ∧
      Module.StablyFree (Localization.Away a) Ω[Localization.Away a⁄R]) ↦
  Filter.eventually_atTop.1
    (@Algebra.IsStrictlyStandard.eventually_pow R A _ _ _ _ a h.1 h.2)

/- Lemma 16.3.7 (8): standard smoothness after inverting `a` eventually makes every sufficiently
large power of `a` elementary standard. -/
@[stacks 07EZ] #check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A)
    (h : Algebra.IsStandardSmooth R (Localization.Away a)) ↦
  Filter.eventually_atTop.1
    (@Algebra.IsElementaryStandard.eventually_pow R A _ _ _ _ a h)
