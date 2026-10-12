/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Counterexample
public import ReasLib.RingTheory.AdicCompletion.RigFlat

@[expose] public section

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- The reduced quotient of the completed principal localization at an element. -/
abbrev reducedCompletedPrincipalLocalization (I : Ideal A) (f : A) : Type u :=
  completedPrincipalLocalization I f ⧸ nilradical (completedPrincipalLocalization I f)

namespace reducedCompletedPrincipalLocalization

/-- The canonical map from the base ring to the reduced completed principal localization. -/
def of (I : Ideal A) (f : A) : A →+* reducedCompletedPrincipalLocalization I f :=
  (Ideal.Quotient.mk (nilradical (completedPrincipalLocalization I f))).comp
    (completedPrincipalLocalization.of I f)

/-- The map of reduced completed principal localizations induced by a ring homomorphism. -/
def mapOf (I : Ideal A) (f : A) :
    completedPrincipalLocalization I f →+*
      completedPrincipalLocalization (I.map (of I f)) (of I f f) := by
  have continuity : (Localization.awayMap (of I f) f).AdicContinuous
      (I.map (algebraMap A (Localization.Away f)))
      ((I.map (of I f)).map
        (algebraMap (reducedCompletedPrincipalLocalization I f)
          (Localization.Away (of I f f)))) := by
    refine ⟨1, ?_⟩
    rw [pow_one, Ideal.map_map, Ideal.map_map]
    have map_comp :
        (Localization.awayMap (of I f) f).comp (algebraMap A (Localization.Away f)) =
          (algebraMap (reducedCompletedPrincipalLocalization I f)
            (Localization.Away (of I f f))).comp (of I f) := by
      ext baseElement
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [map_comp]
  exact continuity.completionMap

end reducedCompletedPrincipalLocalization

namespace AdicCompletion.Counterexample

/-- There is a two-dimensional complete local-domain example whose reduced completed
principal localization is naively rig-flat, although the induced completed-localization map
fails to be naively rig-flat. -/
theorem exists_reduced_completion_not_naively_rig_flat :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (a f : A),
      ringKrullDim A = 2 ∧ IsAdicComplete (Ideal.span {a}) A ∧
        f ∈ IsLocalRing.maximalIdeal A ∧ f ∉ Ideal.span {a} ∧
        ¬ IsReduced
          (Localization.Away
            (algebraMap A (completedPrincipalLocalization (Ideal.span {a}) f) a)) ∧
        Algebra.NaiveRigFlat (Ideal.span {a})
          (reducedCompletedPrincipalLocalization (Ideal.span {a}) f) ∧
        ¬ @Algebra.NaiveRigFlat
            (completedPrincipalLocalization (Ideal.span {a}) f) _
            ((Ideal.span {a}).map
              (completedPrincipalLocalization.of (Ideal.span {a}) f))
            (completedPrincipalLocalization
              ((Ideal.span {a}).map
                (reducedCompletedPrincipalLocalization.of (Ideal.span {a}) f))
              (reducedCompletedPrincipalLocalization.of (Ideal.span {a}) f f))
            _
            (reducedCompletedPrincipalLocalization.mapOf
              (Ideal.span {a}) f).toAlgebra :=
  sorry

end AdicCompletion.Counterexample
