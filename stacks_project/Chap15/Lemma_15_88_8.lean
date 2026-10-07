module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Resolution
import StacksCheckRecall

/-!
# Lemma 15.88.8

@stack 091G
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.88.8 (091G): every derived object over a sequential varying-ring system has a
cochain representative whose stage evaluations are K-flat. -/
@[stacks 091G "representative with stagewise K-flat evaluations"]
#check @SequentialInverseSystem.ModuleSystem.existsCochainRepresentativeWithStagewiseKFlat

#check @SequentialInverseSystem.sequentialRingedModuleCochainEval
#check @CochainComplex.IsKFlat

end
