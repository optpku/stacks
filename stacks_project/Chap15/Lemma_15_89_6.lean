module

public import ReasLib.RingTheory.Module.Support.IdealPower.Torsion
import StacksCheckRecall

/-!
# Lemma 15.89.6

@stack 0953
-/

@[expose] public section

universe u v

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.89.6 (0953): for a finitely generated ideal `I`, the
`I`-power torsion modules are exactly the modules whose support is contained
in `PrimeSpectrum.zeroLocus I`.  In particular the subcategory depends only
on that closed subset. -/
@[stacks 0953]
#check fun (I : Ideal R) (hI : I.FG) ↦
  (Module.isIdealPowerTorsion_iff_support_subset_zeroLocus (M := M) I hI :
    Module.IsIdealPowerTorsion I M ↔
      Module.support R M ⊆ zeroLocus I)

end
