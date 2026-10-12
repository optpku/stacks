/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigFlat.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

/- Example 88.15.3: there exists a local Noetherian two-dimensional domain complete
with respect to a principal ideal whose reduced completed principal localization is
naively rig-flat, while the induced completed-localization map is not. -/
@[stacks 0GGN] #check (AdicCompletion.Counterexample.exists_reduced_completion_not_naively_rig_flat :
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
              (Ideal.span {a}) f).toAlgebra)
