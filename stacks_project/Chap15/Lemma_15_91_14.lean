/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.BeauvilleLaszlo
import StacksCheckRecall

/-!
# Tor of the torsion quotient

Lemma 15.91.14 is the cyclic torsion quotient case of the Beauville-Laszlo Tor vanishing package.
The canonical owner writes `R[f^∞]` as
`Submodule.torsion' R R (Submonoid.powers f)` and is independent of chapter notation.

@stack 0BP0
-/

@[stacks 0BP0 "Lemma 15.91.14"]
#check @CategoryTheory.ModuleCat.Tor.isZero_one_extension_quotientByPowerTorsion_of_glueingPair
