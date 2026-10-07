module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Split
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.119.5

The comparison for the two split rows is owned by
`ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Split`.  Its linear-map equality is the
source-facing form of the determinant-line commuting square, while `splitIso_spec` records the
wedge formula and `switchSign` records the scalar `det(-id_{M ⊗[R] N})`.

@stack 0FJE
-/

/- Lemma 15.119.5: switching the two split summands twists the determinant comparison by the
signed tensor symmetry. -/
@[stacks 0FJE "Lemma 15.119.5: signed symmetry of split determinant comparisons"]
#check @Module.Determinant.Split.commutes

#check @Module.Determinant.Split.splitIso
#check @Module.Determinant.Split.splitIso_spec
#check @Module.Determinant.Split.switchSign
#check @Module.Determinant.Split.switchMap
#check @Module.Determinant.Split.commutes_apply

end
