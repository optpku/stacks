module

public import ReasLib.RingTheory.CohenMacaulay.Module

@[expose] public section

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/-- The ideal depth of a finite Cohen--Macaulay module is the difference between its
support dimension and that of its quotient by the ideal action. -/
theorem idealDepth_eq_supportDim_sub_quotient (I : Ideal R) (hI : I ≠ ⊤) :
    .some (I.depth M) = WithBot.map₂ (fun d e ↦ d - e) (Module.supportDim R M)
      (Module.supportDim R (M ⧸ (I • (⊤ : Submodule R M)))) := sorry

end Module.CohenMacaulay
