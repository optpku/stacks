/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.UniversalFiniteFree
public import ReasLib.RingTheory.Algebra.FreeDimensional

/-!
# Classification of distinguished finite free algebras

The universal structure-constant quotient classifies commutative associative
bilinear multiplications with first basis vector as unit.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace UniversalFiniteFreeAlgebra

variable {R : Type u} [CommRing R] {d : ℕ+}

private theorem classification_linear_apply_eq_sum (g : (Fin d → R) →ₗ[R] (Fin d → R))
    (x : Fin d → R) (k : Fin d) :
    g x k = ∑ i : Fin d, x i * g (Pi.single i 1) k := by
  simpa using
    (congrArg (fun v ↦ g v k) ((Pi.basisFun R (Fin d)).sum_repr x)).symm

/-- The multiplication reconstructed from images of universal coefficients is
associative, commutative, and has the first basis vector as unit. -/
theorem ofRingHom_laws (ψ : CoefficientRing d →+* R) :
    let b := FreeDimAlgebra.mulOfStructureConst (fun i j k ↦ ψ (coefficient d i j k))
    (∀ x y z, b (b x y) z = b x (b y z)) ∧
      (∀ x y, b x y = b y x) ∧
        (∀ x, b (FreeDimAlgebra.one R d) x = x) := by
  let b := FreeDimAlgebra.mulOfStructureConst (fun i j k ↦ ψ (coefficient d i j k))
  change (∀ x y z, b (b x y) z = b x (b y z)) ∧
      (∀ x y, b x y = b y x) ∧
        (∀ x, b (FreeDimAlgebra.one R d) x = x)
  have hsingle (a c n : Fin d) :
      b (Pi.single a 1) (Pi.single c 1) n = ψ (coefficient d a c n) := by
    exact FreeDimAlgebra.mulOfStructureConst_structureConst _ a c n
  have h_assoc_basis (i j k : Fin d) :
      b (b (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1) =
        b (Pi.single i 1) (b (Pi.single j 1) (Pi.single k 1)) := by
    funext m
    calc
      b (b (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1) m =
          ∑ l : Fin d, ψ (coefficient d i j l) * ψ (coefficient d l k m) := by
        simpa only [LinearMap.flip_apply, hsingle] using classification_linear_apply_eq_sum
          (b.flip (Pi.single k 1)) (b (Pi.single i 1) (Pi.single j 1)) m
      _ = ∑ l : Fin d, ψ (coefficient d i l m) * ψ (coefficient d j k l) := by
        simpa only [map_sum, map_mul] using congrArg ψ (coefficient_assoc d i j k m)
      _ = b (Pi.single i 1) (b (Pi.single j 1) (Pi.single k 1)) m := by
        simpa [hsingle, mul_comm] using
          (classification_linear_apply_eq_sum (b (Pi.single i 1))
            (b (Pi.single j 1) (Pi.single k 1)) m).symm
  have h_comm_basis (i j : Fin d) :
      b (Pi.single i 1) (Pi.single j 1) = b (Pi.single j 1) (Pi.single i 1) := by
    funext k
    simpa [hsingle] using congrArg ψ (coefficient_comm d i j k)
  have h_unit_basis (i : Fin d) :
      b (FreeDimAlgebra.one R d) (Pi.single i 1) = Pi.single i 1 := by
    funext k
    change b (Pi.single 0 1) (Pi.single i 1) k = (Pi.single i 1 : Fin d → R) k
    rw [hsingle, coefficient_comm d 0 i k, coefficient_unit]
    by_cases h : i = k <;> simp [h, eq_comm]
  refine ⟨?_, ?_, ?_⟩
  · have h :
        (LinearMap.llcomp R (Fin d → R) (Fin d → R)
          ((Fin d → R) →ₗ[R] (Fin d → R)) b).comp b =
        (LinearMap.llcomp R (Fin d → R) (Fin d → R) (Fin d → R)).compl₁₂ b b := by
      apply (Pi.basisFun R (Fin d)).ext
      intro i
      apply (Pi.basisFun R (Fin d)).ext
      intro j
      apply (Pi.basisFun R (Fin d)).ext
      intro k
      change b (b (Pi.basisFun R (Fin d) i) (Pi.basisFun R (Fin d) j))
          (Pi.basisFun R (Fin d) k) =
        b (Pi.basisFun R (Fin d) i)
          (b (Pi.basisFun R (Fin d) j) (Pi.basisFun R (Fin d) k))
      simpa only [Pi.basisFun_apply] using h_assoc_basis i j k
    intro x y z
    exact congrArg (fun c ↦ c x y z) h
  · have h : b = b.flip := by
      apply (Pi.basisFun R (Fin d)).ext
      intro i
      apply (Pi.basisFun R (Fin d)).ext
      intro j
      change b (Pi.basisFun R (Fin d) i) (Pi.basisFun R (Fin d) j) =
        b (Pi.basisFun R (Fin d) j) (Pi.basisFun R (Fin d) i)
      simpa only [Pi.basisFun_apply] using h_comm_basis i j
    intro x y
    exact congrArg (fun c ↦ c x y) h
  · have h : b (FreeDimAlgebra.one R d) = LinearMap.id := by
      apply (Pi.basisFun R (Fin d)).ext
      intro i
      change b (FreeDimAlgebra.one R d) (Pi.basisFun R (Fin d) i) =
        (Pi.basisFun R (Fin d) i)
      simpa only [Pi.basisFun_apply] using h_unit_basis i
    intro x
    exact congrArg (fun c ↦ c x) h

/-- A ring map from the universal coefficient ring determines the distinguished
algebra whose structure constants are its images of the universal coefficients. -/
def ofRingHom (ψ : CoefficientRing d →+* R) : FreeDimAlgebra R d :=
  FreeDimAlgebra.ofMul
    (FreeDimAlgebra.mulOfStructureConst (fun i j k ↦ ψ (coefficient d i j k)))
    (ofRingHom_laws ψ).1 (ofRingHom_laws ψ).2.1 (ofRingHom_laws ψ).2.2

/-- The structure constants of a distinguished algebra satisfy associativity. -/
theorem structureConst_assoc (m : FreeDimAlgebra R d) (i j k n : Fin d) :
    (∑ l : Fin d, FreeDimAlgebra.structureConst m i j l * FreeDimAlgebra.structureConst m l k n) =
      ∑ l : Fin d, FreeDimAlgebra.structureConst m i l n * FreeDimAlgebra.structureConst m j k l := by
  calc
    (∑ l : Fin d, FreeDimAlgebra.structureConst m i j l *
        FreeDimAlgebra.structureConst m l k n) =
        m.mul (m.mul (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1) n := by
      symm
      exact classification_linear_apply_eq_sum (m.mul.flip (Pi.single k 1))
        (m.mul (Pi.single i 1) (Pi.single j 1)) n
    _ = m.mul (Pi.single i 1) (m.mul (Pi.single j 1) (Pi.single k 1)) n :=
      congrFun (FreeDimAlgebra.mul_assoc m (Pi.single i 1) (Pi.single j 1)
        (Pi.single k 1)) n
    _ = ∑ l : Fin d, FreeDimAlgebra.structureConst m i l n *
        FreeDimAlgebra.structureConst m j k l := by
      rw [classification_linear_apply_eq_sum]
      simp [FreeDimAlgebra.structureConst, mul_comm]

/-- The structure constants of a distinguished algebra are symmetric in their inputs. -/
theorem structureConst_comm (m : FreeDimAlgebra R d) (i j k : Fin d) :
    FreeDimAlgebra.structureConst m i j k = FreeDimAlgebra.structureConst m j i k := by
  exact congrFun (FreeDimAlgebra.mul_comm m (Pi.single i 1) (Pi.single j 1)) k

/-- Structure constants involving the first basis vector are the Kronecker delta. -/
theorem structureConst_unit (m : FreeDimAlgebra R d) (i j : Fin d) :
    FreeDimAlgebra.structureConst m i 0 j = if i = j then 1 else 0 := by
  simpa [FreeDimAlgebra.structureConst, FreeDimAlgebra.one, Pi.single_apply, eq_comm]
    using congrFun (FreeDimAlgebra.mul_one m (Pi.single i 1)) j

/-- Evaluate polynomials at the structure constants of a distinguished algebra. -/
def aevalCoeff (m : FreeDimAlgebra R d) : PolynomialRing d →ₐ[ℤ] R :=
  MvPolynomial.aeval fun (i, j, k) ↦ FreeDimAlgebra.structureConst m i j k

/-- Evaluation at the structure constants annihilates the universal relation ideal. -/
theorem aevalCoeff_mem_relationIdeal (m : FreeDimAlgebra R d) (p : PolynomialRing d)
    (hp : p ∈ relationIdeal d) : aevalCoeff m p = 0 := by
  have h : relationIdeal d ≤ RingHom.ker (aevalCoeff m).toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ((⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩)
    · change aevalCoeff m (associativityRelation d (q 0) (q 1) (q 2) (q 3)) = 0
      simpa [aevalCoeff, associativityRelation, polynomialVariable, map_sum, sub_eq_zero]
        using structureConst_assoc m (q 0) (q 1) (q 2) (q 3)
    · change aevalCoeff m (commutativityRelation d (q 0) (q 1) (q 2)) = 0
      simpa [aevalCoeff, commutativityRelation, polynomialVariable, sub_eq_zero]
        using structureConst_comm m (q 0) (q 1) (q 2)
    · change aevalCoeff m (unitRelation d (q 0) (q 1)) = 0
      by_cases hij : q 0 = q 1 <;>
        simpa [aevalCoeff, unitRelation, polynomialVariable, hij, sub_eq_zero]
          using structureConst_unit m (q 0) (q 1)
  exact h hp

/-- The classifying ring homomorphism of a distinguished algebra is polynomial
evaluation at its structure constants, descended to the universal quotient. -/
def toRingHom (m : FreeDimAlgebra R d) : CoefficientRing d →+* R :=
  Ideal.Quotient.lift (relationIdeal d) (aevalCoeff m).toRingHom
    (fun p hp ↦ aevalCoeff_mem_relationIdeal m p hp)

/-- The universal distinguished algebra is classified by the identity ring map. -/
def universal (d : ℕ+) : FreeDimAlgebra (CoefficientRing d) d :=
  ofRingHom (RingHom.id (CoefficientRing d))

/-- Reconstructing an algebra from a ring map gives the prescribed structure constants. -/
theorem ofRingHom_structureConst (ψ : CoefficientRing d →+* R) (i j k : Fin d) :
    FreeDimAlgebra.structureConst (ofRingHom ψ) i j k = ψ (coefficient d i j k) :=
  FreeDimAlgebra.mulOfStructureConst_structureConst _ i j k

/-- The classifying ring map sends a universal coefficient to the corresponding
structure constant. -/
theorem toRingHom_coefficient (m : FreeDimAlgebra R d) (i j k : Fin d) :
    toRingHom m (coefficient d i j k) = FreeDimAlgebra.structureConst m i j k := by
  simp [toRingHom, coefficient, aevalCoeff, polynomialVariable]

/-- Classifying the algebra reconstructed from a ring map recovers that map. -/
theorem toRingHom_ofRingHom (ψ : CoefficientRing d →+* R) :
    toRingHom (ofRingHom ψ) = ψ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · rintro ⟨i, j, k⟩
    change toRingHom (ofRingHom ψ) (coefficient d i j k) = ψ (coefficient d i j k)
    rw [toRingHom_coefficient, ofRingHom_structureConst]

/-- Reconstructing the algebra from its classifying ring map recovers that algebra. -/
theorem ofRingHom_toRingHom (m : FreeDimAlgebra R d) :
    ofRingHom (toRingHom m) = m := by
  have h : (ofRingHom (toRingHom m)).mul = m.mul := by
    apply (Pi.basisFun R (Fin d)).ext
    intro i
    apply (Pi.basisFun R (Fin d)).ext
    intro j
    funext k
    simp only [Pi.basisFun_apply]
    change FreeDimAlgebra.structureConst (ofRingHom (toRingHom m)) i j k =
      FreeDimAlgebra.structureConst m i j k
    rw [ofRingHom_structureConst, toRingHom_coefficient]
  have h_ext (a b : FreeDimAlgebra R d) (hab : a.mul = b.mul) : a = b := by
    cases a
    cases b
    cases hab
    rfl
  exact h_ext _ _ h

/-- Ring maps from the universal coefficient ring classify distinguished
commutative associative algebra structures with first basis vector as unit. -/
def ringHomEquiv (R : Type u) [CommRing R] (d : ℕ+) :
    (CoefficientRing d →+* R) ≃ FreeDimAlgebra R d where
  toFun := ofRingHom
  invFun := toRingHom
  left_inv := toRingHom_ofRingHom
  right_inv := ofRingHom_toRingHom

/-- The forward classification reconstructs multiplication from coefficient images. -/
theorem ringHomEquiv_apply (ψ : CoefficientRing d →+* R) :
    ringHomEquiv R d ψ = ofRingHom ψ := rfl

/-- The inverse classification is the classifying ring homomorphism. -/
theorem ringHomEquiv_symm_apply (m : FreeDimAlgebra R d) :
    (ringHomEquiv R d).symm m = toRingHom m := rfl

end UniversalFiniteFreeAlgebra
