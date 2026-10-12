/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.CharZero
import StacksCheckRecall

/-!
# Smoothness at a prime in characteristic zero

@stack 00TX
-/

@[expose] public section

@[stacks 00TX "source three-clause form"]
#check @Algebra.IsSmoothAt.charZero_tfae

@[stacks 00TX "regular-local-ring criterion"]
#check @Algebra.IsSmoothAt.iff_isRegularLocalRing_of_separableResidueField

@[stacks 00TX "Kaehler-regularity support"]
#check @KaehlerDifferential.isRegular_of_exists_linearMap_D_eq_one
