module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.119.2

The determinant comparison of a finite-projective short exact row, together with its defining
wedge formula, is owned by the bundled short-complex API.  The same owner also provides the
ordinary linear-map presentation used by the source statement.

@stack 0FJB
-/

/- Lemma 15.119.2: a finite-projective short exact row has its canonical determinant
comparison. -/
@[stacks 0FJB "Lemma 15.119.2: determinant comparison of a short exact row"]
#check @CategoryTheory.ShortComplex.ShortExact.determinantTensorIso

#check @CategoryTheory.ShortComplex.ShortExact.existsUnique_determinantTensorIso
#check @CategoryTheory.ShortComplex.ShortExact.determinantTensorIso_spec
#check @Module.Determinant.shortComplexOfExact
#check @Module.Determinant.shortComplexOfExact_shortExact
#check @Module.Determinant.tensorIsoOfExact
#check @Module.Determinant.tensorIsoOfExact_spec

end
