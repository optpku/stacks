/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Length through a closed fiber

This leaf packages the closed-fiber view of Mathlib's flat local base-change
length formula.  Mathlib's canonical theorem keeps the quotient
`B ⧸ (maximalIdeal A).map (algebraMap A B)` on the right; the declarations here
replace that presentation by the self-module length of `Ideal.Fiber` for the
source-facing closed-fiber API.  No right tensor-algebra instance is exposed:
the fiber factor is intentionally measured over its own ring.

@stack 02M1
@stack 02M2
-/

open IsLocalRing
open scoped TensorProduct

-- `Ideal.Fiber` is a tensor product.  The comparison with its quotient
-- presentation uses the target-ring action on the right tensor factor.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

namespace IsLocalRing

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B]
variable [hABLocal : IsLocalHom (algebraMap A B)] [hABFlat : Module.Flat A B]
variable [AddCommGroup M] [Module A M]

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B] in
/-- The quotient presentation of a closed fiber has the same length as the
fiber measured over itself. -/
theorem length_quotient_eq_fiber :
    Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      Module.length (Ideal.Fiber (maximalIdeal A) B)
        (Ideal.Fiber (maximalIdeal A) B) := by
  calc
    Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
        Module.length B (Ideal.Fiber (maximalIdeal A) B) :=
      (Ideal.Fiber.maximalQuotientAlgEquiv
        (R := A) (S := B) (maximalIdeal A)).toLinearEquiv.length_eq
    _ = Module.length (Ideal.Fiber (maximalIdeal A) B)
        (Ideal.Fiber (maximalIdeal A) B) :=
      Module.length_eq_of_surjective
        (Ideal.Fiber.algebraMap_surjective_of_isMaximal
          (R := A) (S := B) (maximalIdeal A))

/-- `02M1` (closed-fiber length): the flat local base-change length formula with
the closed fiber `Ideal.Fiber (maximalIdeal A) B` measured over itself. -/
@[stacks 02M1 "closed-fiber view of flat local base-change length"]
theorem length_baseChange_eq_mul_fiber :
    Module.length B (B ⊗[A] M) =
      Module.length A M *
        Module.length (Ideal.Fiber (maximalIdeal A) B)
          (Ideal.Fiber (maximalIdeal A) B) := by
  rw [IsLocalRing.length_baseChange]
  rw [length_quotient_eq_fiber]

/-- `02M1` (finite-length closed-fiber criterion): finite length is preserved
and reflected by this flat local base change when the closed fiber has finite
length over itself. -/
@[stacks 02M1 "finite-length criterion through the closed fiber"]
theorem isFiniteLength_baseChange_iff
    (hfiber :
    IsFiniteLength (Ideal.Fiber (maximalIdeal A) B)
        (Ideal.Fiber (maximalIdeal A) B)) :
    IsFiniteLength A M ↔ IsFiniteLength B (B ⊗[A] M) := by
  constructor
  · intro hM
    rw [← Module.length_ne_top_iff] at hM hfiber ⊢
    rw [length_baseChange_eq_mul_fiber]
    exact WithTop.mul_ne_top hM hfiber
  · intro hM
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hM ⊢
    letI : Module.FaithfullyFlat A B :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact hM.imp
      Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      Submodule.IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat

section Tower

variable {C : Type w} [CommRing C] [IsLocalRing C]
variable [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap B C)] [Module.Flat B C]

omit hABLocal hABFlat in
/-- For a composite of flat local homomorphisms, the self-length of the
composite closed fiber is the product of the two closed-fiber lengths. -/
@[stacks 02M2 "multiplicativity of closed-fiber lengths"]
theorem length_fiber_mul_fiber_eq_composite
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] :
    Module.length (Ideal.Fiber (maximalIdeal A) B)
        (Ideal.Fiber (maximalIdeal A) B) *
      Module.length (Ideal.Fiber (maximalIdeal B) C)
        (Ideal.Fiber (maximalIdeal B) C) =
      Module.length (Ideal.Fiber (maximalIdeal A) C)
        (Ideal.Fiber (maximalIdeal A) C) := by
  let Q := B ⧸ (maximalIdeal A).map (algebraMap A B)
  have hmap :
      Ideal.map (algebraMap B C)
          (Ideal.map (algebraMap A B) (maximalIdeal A)) =
        Ideal.map (algebraMap A C) (maximalIdeal A) := by
    simpa [IsScalarTower.algebraMap_eq A B C] using
      (Ideal.map_map (I := maximalIdeal A) (algebraMap A B) (algebraMap B C))
  letI : IsLocalHom (algebraMap A C) := by
    simpa [IsScalarTower.algebraMap_eq A B C] using
      (RingHom.isLocalHom_comp (algebraMap B C) (algebraMap A B))
  letI : Module.Flat A C := Module.Flat.trans A B C
  have hbaseChange :
      Module.length C (C ⊗[B] Q) =
        Module.length B Q *
          Module.length (Ideal.Fiber (maximalIdeal B) C)
            (Ideal.Fiber (maximalIdeal B) C) :=
    length_baseChange_eq_mul_fiber (A := B) (B := C) (M := Q)
  have hTensor :
      Module.length C (C ⊗[B] Q) =
        Module.length (Ideal.Fiber (maximalIdeal A) C)
          (Ideal.Fiber (maximalIdeal A) C) := by
    calc
      Module.length C (C ⊗[B] Q) =
          Module.length C
            (C ⧸ Ideal.map (algebraMap B C)
              (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
        simpa [Q] using
          ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C
            (Ideal.map (algebraMap A B) (maximalIdeal A))).symm.toLinearEquiv.length_eq)
      _ = Module.length C
          (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) := by rw [hmap]
      _ = Module.length (Ideal.Fiber (maximalIdeal A) C)
          (Ideal.Fiber (maximalIdeal A) C) :=
        length_quotient_eq_fiber (A := A) (B := C)
  calc
    Module.length (Ideal.Fiber (maximalIdeal A) B)
          (Ideal.Fiber (maximalIdeal A) B) *
        Module.length (Ideal.Fiber (maximalIdeal B) C)
          (Ideal.Fiber (maximalIdeal B) C) =
      Module.length B Q *
        Module.length (Ideal.Fiber (maximalIdeal B) C)
          (Ideal.Fiber (maximalIdeal B) C) := by
        rw [length_quotient_eq_fiber (A := A) (B := B)]
    _ = Module.length C (C ⊗[B] Q) := hbaseChange.symm
    _ = Module.length (Ideal.Fiber (maximalIdeal A) C)
          (Ideal.Fiber (maximalIdeal A) C) := hTensor

end Tower

end IsLocalRing
