module

import ReasLib.Algebra.Module.Reflexive.Relative.Counterexample
import StacksCheckRecall

universe u

/- Remark 31.12.3: for `k[t³, t⁴, t⁵]`, the dualizing ideal is not reflexive with
respect to the ring, but it is reflexive relative to itself. -/
@[stacks 0AY1] #check
  (Module.RelativeReflexivityCounterexample.dualizingIdeal_reflexivity_counterexample :
    ∀ (k : Type u) [Field k],
      ¬ Module.IsReflexive
          (Module.RelativeReflexivityCounterexample.ring k)
          (Module.RelativeReflexivityCounterexample.dualizingIdeal k) ∧
        Module.IsReflexiveRelativeTo
          (Module.RelativeReflexivityCounterexample.ring k)
          (Module.RelativeReflexivityCounterexample.dualizingIdeal k)
          (Module.RelativeReflexivityCounterexample.dualizingIdeal k))
