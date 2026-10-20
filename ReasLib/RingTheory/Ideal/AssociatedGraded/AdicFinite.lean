module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module

/-!
# Finiteness of adic associated graded modules

This file records the finite-generation property of the associated graded module of a finite
module over an adic completion.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.AssociatedGraded

/-- If `R` is Noetherian and `M` is finite over the `I`-adic completion of `R`, then the
associated graded module of `M`, viewed by restriction of scalars as an `R`-module, is finite
over `gr_I(R)`. -/
theorem gradedModule_finite_of_finite_adicCompletion
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module (AdicCompletion I R) M]
    [Module R M] [IsScalarTower R (AdicCompletion I R) M]
    [Module.Finite (AdicCompletion I R) M] :
    Module.Finite (ring I) (gradedModule I M) := sorry

end Ideal.AssociatedGraded
