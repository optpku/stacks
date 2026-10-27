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
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (v i) := by
  simp [evalToGamma]

/-- A nonzero tuple sends the irrelevant ideal onto the unit ideal of global sections. -/
theorem eval_map_irrelevant_eq_top {R k : Type u} [CommRing R] [Field k]
    (φ : R →+* k) (n : ℕ) {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant (grading R n)).toIdeal.map (evalToGamma φ n v) = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  have hm : MvPolynomial.X i ∈ (HomogeneousIdeal.irrelevant (grading R n)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X R i)
  have hu : IsUnit (evalToGamma φ n v (MvPolynomial.X i)) := by
    rw [evalToGamma_X]
    exact (isUnit_iff_ne_zero.mpr hi).map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hm) hu

/-- The morphism `Spec k ⟶ P^n_R` attached to a nonzero homogeneous coordinate tuple. -/
def homOf {R k : Type u} [CommRing R] [Field k] {n : ℕ} (φ : R →+* k)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    Spec (CommRingCat.of k) ⟶ scheme R n :=
  Proj.fromOfGlobalSections (grading R n) (evalToGamma φ n v)
    (eval_map_irrelevant_eq_top φ n hv)

/-- The morphism attached to a nonzero tuple is a morphism over `Spec R`. -/
theorem homOf_isOver {R k : Type u} [CommRing R] [Field k] {n : ℕ} (φ : R →+* k)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    homOf φ hv ≫ toSpec R n = Spec.map (CommRingCat.ofHom φ) := by
  change homOf φ hv ≫
    (Proj.toSpecZero (grading R n) ≫
      Spec.map (CommRingCat.ofHom (degreeZeroRingEquiv R n).symm.toRingHom)) = _
  rw [← Category.assoc, homOf, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (degreeZeroRingEquiv R n).symm.toRingHom ≫
      CommRingCat.ofHom ((evalToGamma φ n v).comp (algebraMap _ _)) =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of k)).inv := by
    ext r
    change (Scheme.ΓSpecIso (.of k)).inv.hom (MvPolynomial.eval₂Hom φ v
      (MvPolynomial.C r)) = (Scheme.ΓSpecIso (.of k)).inv.hom (φ r)
    simp
  rw [h, Spec.map_comp, ← Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

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
      Over.homMk (homOf φ hv) (homOf_isOver φ hv) := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  apply Over.OverMorphism.ext
  change homOf φ (Projectivization.rep_nonzero (Projectivization.mk k v hv)) = homOf φ hv
  simpa only [ht] using homOf_smul φ hv t

/-- The underlying scheme morphism of `homMk` is the tuple-level map of a representative. -/
theorem homMk_left {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ)
    (x : ℙ k (Fin (n + 1) → k)) :
    (homMk φ n x).left = homOf φ (Projectivization.rep_nonzero x) := rfl

/-- The morphism `Spec k ⟶ P^n_k` attached to a class in `ℙ k (Fin (n + 1) → k)`. -/
def fieldPoint {k : Type u} [Field k] (n : ℕ) (x : ℙ k (Fin (n + 1) → k)) :
    Spec (CommRingCat.of k) ⟶ scheme k n :=
  (homMk (RingHom.id k) n x).left

/-- A field point of `P^n_k` is a section of the structure morphism to `Spec k`. -/
theorem fieldPoint_toSpec {k : Type u} [Field k] (n : ℕ)
    (x : ℙ k (Fin (n + 1) → k)) :
    fieldPoint n x ≫ toSpec k n = 𝟙 (Spec (CommRingCat.of k)) := by
  change homOf (RingHom.id k) (Projectivization.rep_nonzero x) ≫ toSpec k n = _
  simpa using homOf_isOver (RingHom.id k) (Projectivization.rep_nonzero x)

/-- On a standard representative, `fieldPoint` recovers the identity-base tuple morphism. -/
theorem fieldPoint_mk {k : Type u} [Field k] (n : ℕ) {v : Fin (n + 1) → k}
    (hv : v ≠ 0) :
    fieldPoint n (Projectivization.mk k v hv) = homOf (RingHom.id k) hv := by
  exact congrArg (fun f ↦ f.left) (homMk_mk (RingHom.id k) n hv)

/-- Nonzero homogeneous coordinate tuples modulo unit scaling classify the morphisms
`Spec k ⟶ P^n_R` over `Spec R`. -/
theorem homMk_bijective {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ) :
    Function.Bijective (homMk φ n) := sorry

end AlgebraicGeometry.ProjectiveSpace
