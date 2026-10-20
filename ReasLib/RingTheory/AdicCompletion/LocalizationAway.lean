/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.AdicCompletion.Cofinal
public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Completed principal localization

The completed principal localization of a commutative ring `A` at an element `f`
along an ideal `I` is the adic completion of the principal localization
`Localization.Away f` with respect to the extended ideal
`I.map (algebraMap A (Localization.Away f))`.
-/

@[expose] public section

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- The adic completion of the principal localization at `f` along the extended ideal `I`. -/
abbrev completedPrincipalLocalization (I : Ideal A) (f : A) : Type u :=
  AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)

/-- The completed principal localization unfolds to the adic completion of the principal
localization with its extended ideal. -/
theorem completedPrincipalLocalization_def (I : Ideal A) (f : A) :
    completedPrincipalLocalization I f =
      AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f) :=
  sorry

namespace completedPrincipalLocalization

/-- The canonical map from the principal localization to its completed principal localization. -/
abbrev ofAway (I : Ideal A) (f : A) :
    Localization.Away f →+* completedPrincipalLocalization I f :=
  algebraMap (Localization.Away f) (completedPrincipalLocalization I f)

/-- The canonical map from the base ring to the completed principal localization. -/
abbrev of (I : Ideal A) (f : A) : A →+* completedPrincipalLocalization I f :=
  (ofAway I f).comp (algebraMap A (Localization.Away f))

/-- The canonical map from the principal localization is its completion algebra map. -/
theorem ofAway_apply (I : Ideal A) (f : A) (x : Localization.Away f) :
    ofAway I f x = algebraMap (Localization.Away f) (completedPrincipalLocalization I f) x :=
  sorry

/-- The canonical map from the base ring factors through the principal localization. -/
theorem of_apply (I : Ideal A) (f : A) (a : A) :
    of I f a = ofAway I f (algebraMap A (Localization.Away f) a) :=
  sorry

/-- The comparison ring homomorphism induced by a power containment of extended ideals. -/
def comparison (I J : Ideal A) (f : A) (k : ℕ)
    (hIJ : (I.map (algebraMap A (Localization.Away f))) ^ k ≤
      J.map (algebraMap A (Localization.Away f))) :
    completedPrincipalLocalization I f →+* completedPrincipalLocalization J f :=
  AdicCompletion.comparisonRingHomOfPowLe
    (I.map (algebraMap A (Localization.Away f))) (J.map (algebraMap A (Localization.Away f)))
    k hIJ

/-- The comparison map acts by the canonical completion comparison map. -/
theorem comparison_apply (I J : Ideal A) (f : A) (k : ℕ)
    (hIJ : (I.map (algebraMap A (Localization.Away f))) ^ k ≤
      J.map (algebraMap A (Localization.Away f)))
    (x : completedPrincipalLocalization I f) :
    comparison I J f k hIJ x =
      AdicCompletion.comparisonMapOfPowLe
        (I.map (algebraMap A (Localization.Away f))) (J.map (algebraMap A (Localization.Away f)))
        (Localization.Away f) k hIJ x :=
  sorry

/-- The completed principal localization is independent of the ideal of definition. -/
noncomputable def equiv [TopologicalSpace A] [IsTopologicalRing A]
    {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (f : A) :
    completedPrincipalLocalization I f ≃+* completedPrincipalLocalization J f := by
  classical
  let hIJ := TopologicalRing.Ideal.IsIdealOfDefinition.exists_pow_le hI hJ
  let hJI := TopologicalRing.Ideal.IsIdealOfDefinition.exists_pow_le hJ hI
  let c := Nat.find hIJ
  let d := Nat.find hJI
  have hc : 0 < c := (Nat.find_spec hIJ).1
  have hd : 0 < d := (Nat.find_spec hJI).1
  have hIJ' :
      (I.map (algebraMap A (Localization.Away f))) ^ c ≤
        J.map (algebraMap A (Localization.Away f)) := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono (Nat.find_spec hIJ).2
  have hJI' :
      (J.map (algebraMap A (Localization.Away f))) ^ d ≤
        I.map (algebraMap A (Localization.Away f)) := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono (Nat.find_spec hJI).2
  exact AdicCompletion.ringEquivOfPowLe
    (I.map (algebraMap A (Localization.Away f))) (J.map (algebraMap A (Localization.Away f)))
    c d hc hd hIJ' hJI'

/-- The ideal-independence equivalence preserves the canonical image of the principal
localization. -/
theorem equiv_ofAway [TopologicalSpace A] [IsTopologicalRing A]
    {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (f : A)
    (x : Localization.Away f) :
    equiv hI hJ f (ofAway I f x) = ofAway J f x :=
  sorry

end completedPrincipalLocalization
