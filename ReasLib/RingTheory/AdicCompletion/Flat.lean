module

public import ReasLib.CategoryTheory.Monoidal.Tor
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Flatness.Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of completed modules from a first-Tor criterion

This leaf owns the module-flatness clause of the adic completion criterion.  Noetherianity of the
completed ring is already provided independently by `AdicCompletion.isNoetherianRing`.

@stack 0AGW
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Lemma 15.27.5 (2): if `I` is finitely generated, `R ⧸ I` is Noetherian,
`M ⧸ I • ⊤` is flat over `R ⧸ I`, and `Tor₁^R(M, R ⧸ I)` vanishes, then the completion of
`M` is flat over the completion of `R`. -/
@[stacks 0AGW "Lemma 15.27.5 (2)"]
theorem module_flat_of_quotient_flat_of_isZero_tor_one
    [IsNoetherianRing (R ⧸ I)] (hI : I.FG)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor : IsZero
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ I)))) :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) := sorry

end AdicCompletion
