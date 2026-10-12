/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Counterexample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.CoherentFormalModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample

/- Example 52.16.4 -/
@[stacks 0EHE] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.nonAlgebraizable :
    ∀ (k : Type u) [Field k]
      (coefficients : ℕ →
        AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.CoefficientRing k)
      (exponents : ℕ → ℕ),
      ¬ (Scheme.CoherentCompletion.functor
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.idealSheaf k)).essImage
        (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.formalModule
          k coefficients exponents))

/- The zero-higher-coefficient specialization has nontrivial inverse-limit sections. -/
#check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.nontrivialLimit :
    ∀ (k : Type u) [Field k] (exponents : ℕ → ℕ),
      Nontrivial
        (sectionsLimit
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.setup k)
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.formalModule
            k (fun _ ↦ 0) exponents)))

/- Unit higher coefficients with exponential exponents give zero inverse-limit sections. -/
#check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.subsingletonLimit_exponential :
    ∀ (k : Type u) [Field k],
      Subsingleton
        (sectionsLimit
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.setup k)
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.formalModule
            k (fun _ ↦ 1) (fun n ↦ 2 ^ n))))

/- Unit higher coefficients with quadratic exponents give zero inverse-limit sections. -/
#check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.subsingletonLimit_quadratic :
    ∀ (k : Type u) [Field k],
      Subsingleton
        (sectionsLimit
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.setup k)
          (AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample.formalModule
            k (fun _ ↦ 1) (fun n ↦ n ^ 2))))

end AlgebraicGeometry.Scheme.CoherentFormalModules.FormalLineBundleCounterexample
