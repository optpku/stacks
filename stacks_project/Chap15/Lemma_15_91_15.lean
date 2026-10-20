module

public import ReasLib.Algebra.Category.ModuleCat.Tor.BeauvilleLaszlo
import StacksCheckRecall

/-!
# Tor vanishing for a Beauville-Laszlo glueing pair

Lemma 15.91.15 states that `Tor₁^R(R', Coker(M → M_f))` vanishes for every `R`-module `M` when
`(R → R', f)` is a glueing pair.  The reusable owner uses the canonical quotient model
`M_f ⧸ range(M → M_f)`.

@stack 0BP1
-/

-- Lemma 15.91.15: first Tor vanishes on the cokernel of localization.
@[stacks 0BP1 "Lemma 15.91.15"]
#check @CategoryTheory.ModuleCat.Tor.isZero_one_extension_cokernel_toLocalizationAway_of_glueingPair
