/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Noetherian.FiniteGeneration
import StacksCheckRecall

/-!
# Finite generation up to radical

@stack 0G2Z
-/

@[expose] public section

@[stacks 0G2Z "finite generation up to radical"]
#check @Ideal.FGUpToRadical

@[stacks 0G2Z "radical-ideal formulation"]
#check @Ideal.IsRadical.fgUpToRadical_iff

@[stacks 0G2Z "Oka radical identity"]
#check @Ideal.radical_sup_mul_colon

@[stacks 0G2Z "chain condition"]
#check @Ideal.exists_mem_fgUpToRadical_of_sSup

@[stacks 0G2Z "Oka family"]
#check @Ideal.isOka_fgUpToRadical

@[stacks 0G2Z "all-ideal criterion"]
#check @PrimeSpectrum.noetherianSpace_iff_forall_fgUpToRadical

@[stacks 0G2Z "source radical-ideal criterion"]
#check @PrimeSpectrum.noetherianSpace_iff_forall_isRadical_fgUpToRadical

@[stacks 0G2Z "source prime-ideal criterion"]
#check @PrimeSpectrum.noetherianSpace_iff_forall_isPrime_fgUpToRadical
