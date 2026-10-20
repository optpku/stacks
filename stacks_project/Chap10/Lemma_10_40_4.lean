module

public import ReasLib.Algebra.Module.Torsion.BaseChange
import StacksCheckRecall

@[expose] public section

/-! @stack 07T8 -/

/-!
# Lemma 10.40.4

The annihilator comparison is owned by the neutral module-torsion base-change
leaf in ReasLib.  This file is only the source-labelled recall surface.
-/

/- Lemma 10.40.4 (Tag 07T8), element-annihilator clause. -/
@[stacks 07T8 "element-annihilator assertion"]
#check @Ideal.map_torsionOf_eq_baseChange_of_flat

/- Lemma 10.40.4 (Tag 07T8), finite-module annihilator clause. -/
@[stacks 07T8 "finite-module assertion"]
#check @Module.map_annihilator_eq_baseChange_of_flat

end
