module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange.Faithful
import StacksCheckRecall

/-!
# Lemma 15.90.1 (05E7)

The four formal-gluing flatness conditions are owned by the canonical
ideal-power torsion base-change API.

@stack 05E7
-/

@[expose] public section

/- Lemma 15.90.1 (05E7): faithful flatness modulo `I`, surjectivity on
quotient spectra, faithfulness on quotient modules, and faithfulness on
ideal-power torsion modules are equivalent under flatness. -/
@[stacks 05E7]
#check @ModuleCat.IdealPower.BaseChange.faithful_tfae

#check @RingHom.quotientByIdeal
#check @ModuleCat.IdealPower.BaseChange.restricted
