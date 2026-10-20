module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero-Dimensional Integral Extensions

An integral extension of a zero-dimensional commutative ring is again
zero-dimensional.  The ideal-level corollary exposes the corresponding
prime-to-maximal upgrade without specializing the base ring to a field.

@stack 00GS
-/

@[expose] public section

universe u v

namespace RingHom.IsIntegral

/-- An integral extension preserves the property of having Krull dimension at most zero. -/
@[stacks 00GS "integral extensions preserve dimension at most zero"]
theorem krullDimLE_zero
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsIntegral) [Ring.KrullDimLE 0 R] :
    Ring.KrullDimLE 0 S :=
  Ring.KrullDimLE.mk₀ fun I hI ↦ by
    -- Local instance justification (proof-local temporary data): the Going-Up API requires the available primality proof as an instance.
    letI : I.IsPrime := hI
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf I
      (Ideal.isMaximal_of_isPrime (I.comap f))

end RingHom.IsIntegral

namespace Algebra.IsIntegral

/-- Algebra-map companion to `RingHom.IsIntegral.krullDimLE_zero`. -/
@[stacks 00GS "integral algebras preserve dimension at most zero"]
theorem krullDimLE_zero
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Ring.KrullDimLE 0 R] :
    Ring.KrullDimLE 0 S :=
  RingHom.IsIntegral.krullDimLE_zero (f := algebraMap R S)
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S))

end Algebra.IsIntegral

namespace Ideal.IsPrime

/-- A prime ideal in an integral extension of a zero-dimensional ring is maximal. -/
@[stacks 00GS "prime ideals in zero-dimensional integral extensions"]
theorem isMaximal_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Ring.KrullDimLE 0 R]
    {P : Ideal S} (hP : P.IsPrime) : P.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp
    (Algebra.IsIntegral.krullDimLE_zero (R := R) (S := S)) P hP

end Ideal.IsPrime
