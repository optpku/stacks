/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.QuasiSection.Counterexample
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.NoQuasiSection

/- Exercise 111.34.10 -/
@[stacks 029B] #check
  (AlgebraicGeometry.NoQuasiSection.exists_polynomial :
    ∃ f : AlgebraicGeometry.NoQuasiSection.PlaneRing,
      (∀ α : ℂ, ¬ AlgebraicGeometry.NoQuasiSection.linearFactor α ∣ f) ∧
        ¬ AlgebraicGeometry.NoQuasiSection.HasFiniteSurjectiveClosedSubscheme f)

end AlgebraicGeometry.NoQuasiSection
