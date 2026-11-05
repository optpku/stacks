/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra

/-!
# Derivations of chain-graded algebras

This file packages degree-`k` graded derivations as a submodule of the explicit
module of homogeneous linear-map families.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra

variable (A : ChainGradedAlgebra.{u, v} R) (k : ℤ)

/-- The graded Leibniz predicate for a homogeneous linear map of degree `k`.
The sign on a degree-`i` element is `(-1)^(k * i)`. -/
@[stacks 09PR "infrastructure: the graded Leibniz predicate"]
def SatisfiesLeibniz (D : HomogeneousMap A k) : Prop :=
  ∀ i j : ℤ, ∀ a : A.X i, ∀ b : A.X j,
    D (i + j) (A.mul i j a b) =
      A.reindex (add_right_comm i k j)
          (A.mul (i + k) j (D i a) b) +
        (k * i).negOnePow •
          A.reindex (add_assoc i j k).symm
            (A.mul i (j + k) a (D j b))

namespace SatisfiesLeibniz

/-- The zero homogeneous map satisfies the graded Leibniz rule. -/
theorem zero : SatisfiesLeibniz A k (0 : HomogeneousMap A k) := sorry

/-- The sum of two maps satisfying the graded Leibniz rule again satisfies it. -/
theorem add {D E : HomogeneousMap A k} (hD : SatisfiesLeibniz A k D)
    (hE : SatisfiesLeibniz A k E) : SatisfiesLeibniz A k (D + E) := sorry

/-- A scalar multiple of a map satisfying the graded Leibniz rule again satisfies it. -/
theorem smul (r : R) {D : HomogeneousMap A k} (hD : SatisfiesLeibniz A k D) :
    SatisfiesLeibniz A k (r • D) := sorry

end SatisfiesLeibniz

/-- The `R`-submodule of degree-`k` homogeneous maps satisfying
the graded Leibniz rule. -/
@[stacks 09PR "infrastructure: the submodule of graded derivations"]
def derivationSubmodule : Submodule R (HomogeneousMap A k) where
  carrier := {D | SatisfiesLeibniz A k D}
  zero_mem' := SatisfiesLeibniz.zero A k
  add_mem' := SatisfiesLeibniz.add A k
  smul_mem' := SatisfiesLeibniz.smul A k

/-- Membership in `derivationSubmodule A k` is the graded Leibniz rule. -/
theorem mem_derivationSubmodule (D : HomogeneousMap A k) :
    D ∈ derivationSubmodule A k ↔ SatisfiesLeibniz A k D := sorry

/-- A degree-`k` graded derivation of `A`. -/
@[stacks 09PR "infrastructure: graded derivations"]
abbrev Derivation := derivationSubmodule A k

namespace Derivation

variable {A : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- The homogeneous linear-map family underlying a graded derivation. -/
def toHomogeneousMap (D : Derivation A k) : HomogeneousMap A k :=
  D.1

/-- A graded derivation acts on each homogeneous component. -/
instance instCoeFun : CoeFun (Derivation A k)
    (fun _ ↦ ∀ i : ℤ, A.X i → A.X (i + k)) where
  coe D := fun i x ↦ toHomogeneousMap D i x

/-- Evaluation of a derivation is evaluation of its underlying homogeneous map. -/
@[simp]
theorem coe_apply (D : Derivation A k) (i : ℤ) (x : A.X i) :
    D i x = toHomogeneousMap D i x := sorry

/-- A graded derivation satisfies the graded Leibniz predicate. -/
theorem satisfiesLeibniz (D : Derivation A k) :
    SatisfiesLeibniz A k (toHomogeneousMap D) := sorry

/-- The graded Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (D : Derivation A k) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    D (i + j) (A.mul i j a b) =
      A.reindex (add_right_comm i k j)
          (A.mul (i + k) j (D i a) b) +
        (k * i).negOnePow •
          A.reindex (add_assoc i j k).symm
            (A.mul i (j + k) a (D j b)) := sorry

/-- Derivations are determined by their values on homogeneous elements. -/
@[ext]
theorem ext {D E : Derivation A k}
    (h : ∀ i : ℤ, ∀ x : A.X i, D i x = E i x) : D = E := sorry

/-- The zero derivation is pointwise zero. -/
@[simp]
theorem zero_apply (i : ℤ) (x : A.X i) :
    (0 : Derivation A k) i x = 0 := sorry

/-- Addition of derivations is pointwise addition. -/
@[simp]
theorem add_apply (D E : Derivation A k) (i : ℤ) (x : A.X i) :
    (D + E) i x = D i x + E i x := sorry

/-- Scalar multiplication of derivations is pointwise scalar multiplication. -/
@[simp]
theorem smul_apply (r : R) (D : Derivation A k) (i : ℤ) (x : A.X i) :
    (r • D) i x = r • D i x := sorry

end Derivation

namespace HomogeneousMap

variable {A B : ChainGradedAlgebra.{u, v} R} {k l : ℤ}

/-- Change the homogeneous modules by explicit degreewise linear equivalences. -/
def conj (e : ∀ i, A.X i ≃ₗ[R] B.X i) (D : HomogeneousMap A k) :
    HomogeneousMap B k :=
  fun i ↦ (e (i + k)).toLinearMap.comp ((D i).comp (e i).symm.toLinearMap)

/-- Degreewise linear maps commute with transport between equal degrees. -/
theorem equiv_reindex (e : ∀ i, A.X i ≃ₗ[R] B.X i) {i j : ℤ}
    (h : i = j) (x : A.X i) :
    e j (A.reindex h x) = B.reindex h (e i x) := by
  cases h
  rfl

@[simp]
theorem conj_apply (e : ∀ i, A.X i ≃ₗ[R] B.X i) (D : HomogeneousMap A k)
    (i : ℤ) (x : B.X i) :
    conj e D i x = e (i + k) (D i ((e i).symm x)) := rfl

@[simp]
theorem conj_symm_conj (e : ∀ i, A.X i ≃ₗ[R] B.X i) (D : HomogeneousMap A k) :
    conj (fun i ↦ (e i).symm) (conj e D) = D := by
  funext i
  apply LinearMap.ext
  intro x
  simp only [conj_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

@[simp]
theorem conj_units_smul (e : ∀ i, A.X i ≃ₗ[R] B.X i) (r : ℤˣ)
    (D : HomogeneousMap A k) : conj e (r • D) = r • conj e D := by
  funext i
  apply LinearMap.ext
  intro x
  change e (i + k) ((r : ℤ) • D i ((e i).symm x)) =
    (r : ℤ) • e (i + k) (D i ((e i).symm x))
  exact map_zsmul (e (i + k)) (r : ℤ) (D i ((e i).symm x))

/-- Conjugation commutes with composition, including the degree reassociation. -/
theorem conj_comp (e : ∀ i, A.X i ≃ₗ[R] B.X i)
    (D : HomogeneousMap A k) (E : HomogeneousMap A l) :
    conj e (comp E D) = comp (conj e E) (conj e D) := by
  funext i
  apply LinearMap.ext
  intro x
  simp only [conj_apply, comp, LinearMap.comp_apply, LinearEquiv.symm_apply_apply,
    equiv_reindex]

/-- Conjugation commutes with a change of the homogeneous degree. -/
theorem conj_castDegree (e : ∀ i, A.X i ≃ₗ[R] B.X i) (h : k = l)
    (D : HomogeneousMap A k) :
    conj e (castDegree h D) = castDegree h (conj e D) := by
  cases h
  rfl

/-- Graded commutation is invariant under degreewise conjugation. -/
theorem conj_gradedCommutes_iff (e : ∀ i, A.X i ≃ₗ[R] B.X i)
    (D : HomogeneousMap A k) (E : HomogeneousMap A l) :
    GradedCommutes (conj e D) (conj e E) ↔ GradedCommutes D E := by
  have forward (h : GradedCommutes D E) :
      GradedCommutes (conj e D) (conj e E) := by
    unfold GradedCommutes at h ⊢
    rw [← conj_comp, h, conj_units_smul, conj_castDegree, conj_comp]
  refine ⟨fun h ↦ ?_, forward⟩
  unfold GradedCommutes at h ⊢
  have h' := congrArg (conj (fun i ↦ (e i).symm)) h
  simpa only [← conj_comp, conj_units_smul, conj_castDegree,
    conj_symm_conj] using h'

end HomogeneousMap

namespace Derivation

variable {A B : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- Explicit transport of a derivation along multiplicative degreewise linear equivalences. -/
def transport (e : ∀ i, A.X i ≃ₗ[R] B.X i)
    (hmul : ∀ i j (x : A.X i) (y : A.X j),
      e (i + j) (A.mul i j x y) = B.mul i j (e i x) (e j y))
    (D : Derivation A k) : Derivation B k := by
  refine ⟨HomogeneousMap.conj e (toHomogeneousMap D), ?_⟩
  change SatisfiesLeibniz B k _
  intro i j x y
  have hm : (e (i + j)).symm (B.mul i j x y) =
      A.mul i j ((e i).symm x) ((e j).symm y) := by
    apply (e (i + j)).injective
    simp only [LinearEquiv.apply_symm_apply, hmul]
  simp only [HomogeneousMap.conj_apply, hm, toHomogeneousMap]
  rw [D.2 i j ((e i).symm x) ((e j).symm y), map_add, Units.smul_def, map_zsmul,
    HomogeneousMap.equiv_reindex, HomogeneousMap.equiv_reindex, hmul, hmul]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- The transported derivation has the explicitly conjugated homogeneous map. -/
theorem transport_toHomogeneousMap (e : ∀ i, A.X i ≃ₗ[R] B.X i)
    (hmul : ∀ i j (x : A.X i) (y : A.X j),
      e (i + j) (A.mul i j x y) = B.mul i j (e i x) (e j y))
    (D : Derivation A k) :
    toHomogeneousMap (transport e hmul D) =
      HomogeneousMap.conj e (toHomogeneousMap D) := rfl

end Derivation

end ChainGradedAlgebra
