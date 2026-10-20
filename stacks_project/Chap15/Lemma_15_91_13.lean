module

public import ReasLib.Algebra.Category.ModuleCat.Tor.BeauvilleLaszlo

import StacksCheckRecall

/-!
# Tor of positive principal-power ideals

The first-Tor vanishing for principal-power ideals in a Beauville-Laszlo glueing pair is owned by
`CategoryTheory.ModuleCat.Tor.isZero_one_extension_principalPowerIdeal_of_glueingPair`.

@stack 0BNZ
-/

-- Lemma 15.91.13: `Tor₁^R(R', f ^ n R) = 0` for every positive `n`.
@[stacks 0BNZ "Lemma 15.91.13"]
#check @CategoryTheory.ModuleCat.Tor.isZero_one_extension_principalPowerIdeal_of_glueingPair
