module

public import ReasLib.RingTheory.CohenMacaulay.SystemOfParameters
import StacksCheckRecall

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

/- Definition 111.28.1: a Noetherian local ring of dimension `d` is Cohen–Macaulay
exactly when it admits a system of parameters whose entries are nonzerodivisors on
the successive prefix quotients. -/
@[stacks 0285] #check
  (Module.CohenMacaulay.iff_exists_isSystemOfParameters_isRegular :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (d : ℕ),
      Module.CohenMacaulay R R ∧ ringKrullDim R = d ↔
        ∃ x : Fin d → maximalIdeal R,
          IsSystemOfParameters x ∧ IsRegular R (List.ofFn fun i ↦ (x i : R)))
