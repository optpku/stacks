module

public import Mathlib.RingTheory.QuotSMulTop
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Cokernel
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace Module.Flat

/-- If multiplication by an element of the target maximal ideal is injective on the
closed-fiber quotient of a finite module flat over the source, then the quotient by that
element remains flat over the source. -/
@[stacks 0252]
theorem quotSMulTop_of_mod_maximalIdeal_injective
    {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.Flat A M]
    (t : B) (ht : t ∈ IsLocalRing.maximalIdeal B)
    (hmod : Function.Injective
      (((LinearMap.lsmul B M t).restrictScalars A).quotientMapByIdeal
        (IsLocalRing.maximalIdeal A))) :
    Module.Flat A (QuotSMulTop t M) := sorry

end Module.Flat
