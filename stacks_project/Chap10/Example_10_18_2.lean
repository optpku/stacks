/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.LocalHom
import StacksCheckRecall

/-!
# Local maps into prime localizations

@stack 0H70
-/

@[expose] public section

@[stacks 0H70 "prime-localization locality criterion"]
#check @Localization.AtPrime.isLocalHom_iff_comap_maximalIdeal

@[stacks 0H70 "local homomorphism maximal-ideal contraction"]
#check @IsLocalRing.maximalIdeal_comap

@[stacks 0H70 "localization-at-prime maximal ideal"]
#check @Localization.AtPrime.under_maximalIdeal
