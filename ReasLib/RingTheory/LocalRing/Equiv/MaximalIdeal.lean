module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Equiv

@[expose] public section

/-!
# Maximal-ideal quotient powers under local ring equivalences

This leaf specializes mathlib's `Ideal.quotientEquiv` to the powers of the
maximal ideals of local rings.  It is independent of completions, so the
same finite-stage equivalences are available to any inverse-system argument.
-/

open IsLocalRing

namespace RingEquiv.MaximalIdeal

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- A local-ring equivalence maps each power of the source maximal ideal onto the
corresponding power of the target maximal ideal. -/
@[simp]
theorem map_pow_eq (e : A ≃+* B) (n : ℕ) :
    Ideal.map e.toRingHom (maximalIdeal A ^ n) = maximalIdeal B ^ n := sorry

/-- Contracting a power of the target maximal ideal along a local-ring equivalence recovers
the corresponding source power. -/
@[simp]
theorem comap_pow_eq (e : A ≃+* B) (n : ℕ) :
    Ideal.comap e.toRingHom (maximalIdeal B ^ n) = maximalIdeal A ^ n := sorry

/-- The canonical equivalence between the quotients by corresponding maximal-ideal powers
of equivalent local rings. -/
@[stacks 0CAR "maximal-ideal quotient powers under a ring equivalence"]
def quotientPowEquiv (e : A ≃+* B) (n : ℕ) :
    A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  Ideal.quotientEquiv (maximalIdeal A ^ n) (maximalIdeal B ^ n) e
    ((Ideal.map_pow e.toRingHom (maximalIdeal A) n).trans
      (congrArg (fun I : Ideal B => I ^ n)
        (IsLocalRing.map_ringEquiv_maximalIdeal e))).symm

/-- `quotientPowEquiv` sends a source quotient class to the class of its image. -/
theorem quotientPowEquiv_mk (e : A ≃+* B) (n : ℕ) (a : A) :
    quotientPowEquiv e n (Ideal.Quotient.mk (maximalIdeal A ^ n) a) =
      Ideal.Quotient.mk (maximalIdeal B ^ n) (e a) := sorry

/-- The inverse of `quotientPowEquiv` sends a target quotient class to the class of its
inverse image. -/
theorem quotientPowEquiv_symm_mk (e : A ≃+* B) (n : ℕ) (b : B) :
    (quotientPowEquiv e n).symm (Ideal.Quotient.mk (maximalIdeal B ^ n) b) =
      Ideal.Quotient.mk (maximalIdeal A ^ n) (e.symm b) := sorry

/-- The maximal-ideal quotient-power equivalences commute with the canonical transition maps. -/
@[stacks 0CAR "naturality of maximal-ideal quotient powers"]
theorem factorPow_comp_quotientPowEquiv (e : A ≃+* B)
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp
        (quotientPowEquiv e n).toRingHom =
      (quotientPowEquiv e m).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal A) h) := sorry

end RingEquiv.MaximalIdeal
