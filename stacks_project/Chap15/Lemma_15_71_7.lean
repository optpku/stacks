module

public import ReasLib.Algebra.Module.IdealProjective.Dual
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.7

@stack 0G96
-/

/-!
# Lemma 15.71.7: duals of finite ideal-projective modules
-/

/- Lemma 15.71.7: the dual of a finite ideal-projective module is ideal-projective. -/
@[stacks 0G96]
#check @Module.IsIdealProjective.dual

/- Strong ideal-valued form. -/
#check @Module.projectiveFactorIdeal.le_dual

/- Dualization acts on the structured finite-projective factorisation itself. -/
#check @LinearMap.Factorisation.FiniteProjective.dualMap
