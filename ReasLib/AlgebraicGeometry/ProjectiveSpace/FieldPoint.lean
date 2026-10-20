/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over

/-!
# Field-valued points of standard projective space

Nonzero homogeneous coordinate tuples define morphisms `Spec k ⟶ P^n_R`.
Their classes in `ℙ k (Fin (n + 1) → k)` classify the morphisms over `Spec R`.
The identity-base specialization gives morphisms `Spec k ⟶ P^n_k`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Evaluate the homogeneous coordinate ring of `P^n_R` at a tuple in `k^{n+1}` and
view the result in global sections of `Spec k`. -/
def evalToGamma {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    (v : Fin (n + 1) → k) :
    MvPolynomial (Fin (n + 1)) R →+* Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp (MvPolynomial.eval₂Hom φ v)

/-- Evaluation of a coordinate polynomial recovers the corresponding tuple entry. -/
theorem evalToGamma_X {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    (v : Fin (n + 1) → k) (i : Fin (n + 1)) :
    evalToGamma φ n v (MvPolynomial.X i) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (v i) := sorry

/-- A nonzero tuple sends the irrelevant ideal onto the unit ideal of global sections. -/
theorem eval_map_irrelevant_eq_top {R k : Type u} [CommRing R] [Field k]
    (φ : R →+* k) (n : ℕ) {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant (grading R n)).toIdeal.map (evalToGamma φ n v) = ⊤ := sorry

/-- The morphism `Spec k ⟶ P^n_R` attached to a nonzero homogeneous coordinate tuple. -/
def homOf {R k : Type u} [CommRing R] [Field k] {n : ℕ} (φ : R →+* k)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    Spec (CommRingCat.of k) ⟶ scheme R n :=
  Proj.fromOfGlobalSections (grading R n) (evalToGamma φ n v)
    (eval_map_irrelevant_eq_top φ n hv)

/-- The morphism attached to a nonzero tuple is a morphism over `Spec R`. -/
theorem homOf_isOver {R k : Type u} [CommRing R] [Field k] {n : ℕ} (φ : R →+* k)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    homOf φ hv ≫ toSpec R n = Spec.map (CommRingCat.ofHom φ) := sorry

/-- Scaling a nonzero tuple by a unit of `k` does not change the associated morphism. -/
theorem homOf_smul {R k : Type u} [CommRing R] [Field k] {n : ℕ} (φ : R →+* k)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) (t : kˣ) :
    homOf φ ((smul_ne_zero_iff_ne t).mpr hv) = homOf φ hv := sorry

/-- The slice morphism `Spec k ⟶ P^n_R` over `Spec R` attached to a class in
`ℙ k (Fin (n + 1) → k)`. -/
def homMk {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    (x : ℙ k (Fin (n + 1) → k)) :
    Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ schemeOver R n :=
  Over.homMk (homOf φ (Projectivization.rep_nonzero x))
    (homOf_isOver φ (Projectivization.rep_nonzero x))

/-- On a standard representative, `homMk` recovers the tuple-level constructor. -/
theorem homMk_mk {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    homMk φ n (Projectivization.mk k v hv) =
      Over.homMk (homOf φ hv) (homOf_isOver φ hv) := sorry

/-- The underlying scheme morphism of `homMk` is the tuple-level map of a representative. -/
theorem homMk_left {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    (x : ℙ k (Fin (n + 1) → k)) :
    (homMk φ n x).left = homOf φ (Projectivization.rep_nonzero x) := sorry

/-- The morphism `Spec k ⟶ P^n_k` attached to a class in `ℙ k (Fin (n + 1) → k)`. -/
def fieldPoint {k : Type u} [Field k] (n : ℕ) (x : ℙ k (Fin (n + 1) → k)) :
    Spec (CommRingCat.of k) ⟶ scheme k n :=
  (homMk (RingHom.id k) n x).left

/-- A field point of `P^n_k` is a section of the structure morphism to `Spec k`. -/
theorem fieldPoint_toSpec {k : Type u} [Field k] (n : ℕ)
    (x : ℙ k (Fin (n + 1) → k)) :
    fieldPoint n x ≫ toSpec k n = 𝟙 (Spec (CommRingCat.of k)) := sorry

/-- On a standard representative, `fieldPoint` recovers the identity-base tuple morphism. -/
theorem fieldPoint_mk {k : Type u} [Field k] (n : ℕ) {v : Fin (n + 1) → k}
    (hv : v ≠ 0) :
    fieldPoint n (Projectivization.mk k v hv) = homOf (RingHom.id k) hv := sorry

/-- Nonzero homogeneous coordinate tuples modulo unit scaling classify the morphisms
`Spec k ⟶ P^n_R` over `Spec R`. -/
theorem homMk_bijective {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ) :
    Function.Bijective (homMk φ n) := sorry

end AlgebraicGeometry.ProjectiveSpace
