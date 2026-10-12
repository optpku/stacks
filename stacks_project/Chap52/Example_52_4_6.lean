/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalSections.Sharpness
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

/- Example 52.4.6 -/
@[stacks 0EH8] #check
  (FormalSectionsSharpness.rationalSectionPowersConverges :
    ∀ (k : Type u) [Field k],
      FormalSectionsSharpness.VanishesAtOwnStage k
          (FormalSectionsSharpness.rationalSectionPowerValues k) ∧
        FormalSectionsSharpness.ConvergesToZero k
          (FormalSectionsSharpness.rationalSectionPowerValues k))

#check
  (FormalSectionsSharpness.rationalSectionPowersAvoidIdeal :
    ∀ (k : Type u) [Field k],
      FormalSectionsSharpness.AvoidsIdealMultiple k
        (FormalSectionsSharpness.rationalSectionPowerValues k))

#check
  (FormalSectionsSharpness.localCohomologyDimension_eq_two :
    ∀ (k : Type u) [Field k],
      Ideal.LocalCohomology.dimension (FormalSectionsSharpness.idealI k)
          (FormalSectionsSharpness.idealI k).fg_of_isNoetherianRing = 2)
