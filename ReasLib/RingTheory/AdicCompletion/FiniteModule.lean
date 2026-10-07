module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

@[expose] public section

universe u v

namespace AdicCompletion

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- The adic completion of a finite module is finite over the completed ring. -/
instance instModuleFinite [Module.Finite A M] :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := sorry

end AdicCompletion
