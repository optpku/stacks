/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universe lifts of quotient rings

This leaf owns the canonical comparison between quotienting a lifted ring by
the mapped ideal and lifting the original quotient ring.

@stack 051I
-/

universe u v w

namespace Ideal

variable {A : Type u} [CommRing A]

/-- Mapping an ideal to `ULift A` and back along the canonical algebra equivalence recovers the
original ideal. -/
theorem map_ulift_algebraMap_algEquiv (J : Ideal A) :
    J =
      (J.map (algebraMap A (ULift.{v} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{v} A ≃ₐ[A] A) : ULift.{v} A →+* A) := by
  let e : ULift.{v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  calc
    J = J.map (RingHom.id A) := by simp
    _ = J.map ((e : ULift.{v} A →+* A).comp (algebraMap A (ULift.{v} A))) := by
      ext a
      rfl
    _ = (J.map (algebraMap A (ULift.{v} A))).map (e : ULift.{v} A →+* A) := by
      rw [Ideal.map_map]

/-- The quotient of a lifted commutative `R`-algebra by a mapped ideal is canonically
`R`-algebra-equivalent to the original quotient. -/
@[stacks 051I]
noncomputable def uliftQuotientAlgEquiv {R : Type w} [CommSemiring R] [Algebra R A]
    (J : Ideal A) :
    (ULift.{v} A ⧸ J.map (algebraMap A (ULift.{v} A))) ≃ₐ[R] A ⧸ J := by
  let e : ULift.{v} A ≃ₐ[R] A := ULift.algEquiv (R := R) (A := A)
  have h_map : J = (J.map (algebraMap A (ULift.{v} A))).map (e : ULift.{v} A →+* A) := by
    calc
      J = J.map (RingHom.id A) := by simp
      _ = J.map ((e : ULift.{v} A →+* A).comp (algebraMap A (ULift.{v} A))) := by
        ext a
        rfl
      _ = (J.map (algebraMap A (ULift.{v} A))).map (e : ULift.{v} A →+* A) := by
        rw [Ideal.map_map]
  exact Ideal.quotientEquivAlg _ _ e h_map

@[simp]
theorem uliftQuotientAlgEquiv_mk {R : Type w} [CommSemiring R] [Algebra R A]
    (J : Ideal A) (a : ULift.{v} A) :
    uliftQuotientAlgEquiv (R := R) J
        (Ideal.Quotient.mk (J.map (algebraMap A (ULift.{v} A))) a) =
      Ideal.Quotient.mk J a.down :=
  rfl

@[simp]
theorem uliftQuotientAlgEquiv_symm_mk {R : Type w} [CommSemiring R] [Algebra R A]
    (J : Ideal A) (a : A) :
    (uliftQuotientAlgEquiv (R := R) J).symm (Ideal.Quotient.mk J a) =
      Ideal.Quotient.mk (J.map (algebraMap A (ULift.{v} A))) (ULift.up a) :=
  rfl

/-- The quotient of a lifted commutative ring by the mapped ideal is canonically ring-equivalent
to the original quotient.  This is the scalar-forgotten form of
`uliftQuotientAlgEquiv`, so its concrete equivalence data does not depend on a proof placeholder. -/
@[stacks 051I]
noncomputable def uliftQuotientRingEquiv (J : Ideal A) :
    (ULift.{v} A ⧸ J.map (algebraMap A (ULift.{v} A))) ≃+* A ⧸ J :=
  (uliftQuotientAlgEquiv (R := A) J).toRingEquiv

end Ideal
