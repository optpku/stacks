module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

universe u v w

namespace IsNormalRing

/-- A finite injective extension of finite algebras over a Noetherian local ring transfers
normality from the source and completed target to the completion of the source. -/
@[stacks 0BGH]
theorem adicCompletion_of_finite_injective
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (B : Type v) (C : Type w) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C]
    (f : B →ₐ[A] C) (hf : Function.Injective f) [IsNormalRing B]
    [IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A)) C)] :
    IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B) := sorry

end IsNormalRing
