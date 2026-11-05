/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Pairing
import all ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Complex

/-!
# Degree-shifted pairings on the relative tensor complex
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex

namespace DifferentialGradedModule.TensorProduct

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

/-- A degree-`k` bilinear pairing from a right-left pair of DG modules to a cochain complex.
Its component on bidegree `(p, q)` lands directly in degree `(p + q) + k`. -/
abbrev GradedPairing (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    (P : CochainComplex (ModuleCat.{max v w} R) ℤ) (k : ℤ) :=
  (p q : ℤ) → baseTensor (R := R) (M.X p) (N.X q) ⟶ P.X ((p + q) + k)

/-- Extend a degree-`k` pairing to the unbalanced total tensor term in one degree. -/
def gradedRawDesc (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (n : ℤ) :
    rawTerm M N n →ₗ[R] P.X (n + k) :=
  (mapBifunctorDesc (K₁ := rightComplex M) (K₂ := leftComplex N)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ φ p q ≫ eqToHom (congrArg (fun t : ℤ ↦ P.X (t + k)) h))).hom

private theorem gradedRawDesc_ι (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (p q n : ℤ) (h : p + q = n)
    (z : baseTensor (R := R) (M.X p) (N.X q)) :
    gradedRawDesc M N φ n
        ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) p q n h).hom z) =
      cast (congrArg (fun t : ℤ ↦ (P.X (t + k) : Type (max v w))) h) (φ p q z) := by
  subst n
  exact congrArg
    (fun f : baseTensor (R := R) (M.X p) (N.X q) ⟶ P.X ((p + q) + k) ↦ f z)
    (ι_mapBifunctorDesc
      (K₁ := rightComplex M) (K₂ := leftComplex N) (F := baseBifunctor (R := R))
      (c := up ℤ)
      (fun a b h ↦ φ a b ≫ eqToHom (congrArg (fun t : ℤ ↦ P.X (t + k)) h)) p q rfl)

/-- A degree-shifted pairing is balanced when the two homogeneous actions of `A` agree
elementwise. -/
def GradedIsBalanced (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) : Prop :=
  ∀ (p i q : ℤ) (m : M.X p) (a : A.X i) (x : N.X q),
    φ (p + i) q (M.smul p i m a ⊗ₜ[R] x) =
      cast (congrArg (fun n : ℤ ↦ (P.X (n + k) : Type (max v w)))
        (add_assoc p i q).symm) (φ p (i + q) (m ⊗ₜ[R] N.smul i q a x))

/-- Elementwise degree-shifted balancing is equivalent to killing the generated balancing
relations in every total degree. -/
theorem gradedIsBalanced_iff_relations_le_ker
    (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) :
    GradedIsBalanced M N φ ↔
      ∀ n, relations M N n ≤ LinearMap.ker (gradedRawDesc M N φ n) := by
  constructor
  · intro hφ n
    apply Submodule.span_le.mpr
    rintro z ⟨p, i, q, h, m, a, x, rfl⟩
    subst n
    change gradedRawDesc M N φ _ (balanceGenerator M N p i q _ rfl m a x) = 0
    rw [balanceGenerator, map_sub, gradedRawDesc_ι, gradedRawDesc_ι]
    exact sub_eq_zero.mpr (hφ p i q m a x)
  · intro hφ p i q m a x
    have hz := hφ ((p + i) + q) (Submodule.subset_span
      (show balanceGenerator M N p i q _ rfl m a x ∈ _ from
        ⟨p, i, q, rfl, m, a, x, rfl⟩))
    change gradedRawDesc M N φ _ (balanceGenerator M N p i q _ rfl m a x) = 0 at hz
    rw [balanceGenerator, map_sub, gradedRawDesc_ι, gradedRawDesc_ι] at hz
    exact sub_eq_zero.mp hz

/-- Descend a balanced degree-`k` pairing to one degree of the relative tensor quotient. -/
def gradedDescLinear (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ) (n : ℤ) :
    family M N n →ₗ[R] P.X (n + k) :=
  (relations M N n).liftQ (gradedRawDesc M N φ n)
    ((gradedIsBalanced_iff_relations_le_ker M N φ).mp hφ n)

/-- Reindex the first Leibniz summand for a degree-`k` pairing. -/
theorem gradedDifferentialLeftDegree (p q k : ℤ) :
    ((p + 1) + q) + k = ((p + q) + k) + 1 := by
  ac_rfl

/-- Reindex the second Leibniz summand for a degree-`k` pairing. -/
theorem gradedDifferentialRightDegree (p q k : ℤ) :
    (p + (q + 1)) + k = ((p + q) + k) + 1 := by
  ac_rfl

/-- A degree-`k` pairing is differential-compatible when it intertwines differentials with the
usual sign `(-1)^k` on the source differential. -/
def GradedIsDifferentialCompatible (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) : Prop :=
  ∀ (p q : ℤ) (m : M.X p) (x : N.X q),
    P.d ((p + q) + k) (((p + q) + k) + 1) (φ p q (m ⊗ₜ[R] x)) =
      (k.negOnePow : R) •
        (cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
            (gradedDifferentialLeftDegree p q k))
              (φ (p + 1) q (M.d p m ⊗ₜ[R] x)) +
          (p.negOnePow : R) •
            cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
              (gradedDifferentialRightDegree p q k))
                (φ p (q + 1) (m ⊗ₜ[R] N.d q x)))

/-- Section 22.12 (09LL): a balanced degree-`k` pairing induces a degree-`k` cochain from the
relative tensor complex. -/
@[stacks 09LL "degree-shifted relative tensor universal map"]
def gradedLift (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ) :
    Cochain (complex M N) P k :=
  Cochain.mk fun n _ h ↦ ModuleCat.ofHom <|
    ModuleCat.castLinearMap (congrArg P.X h) (gradedDescLinear M N φ hφ n)

/-- The cochain induced by a balanced degree-shifted pairing evaluates on a pure tensor by the
original pairing. -/
@[simp]
theorem gradedLift_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ)
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    (gradedLift M N φ hφ).v (p + q) ((p + q) + k) rfl (tmul M N m x) =
      φ p q (m ⊗ₜ[R] x) := by
  change gradedRawDesc M N φ (p + q)
    ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
      (up ℤ) p q (p + q) rfl).hom (m ⊗ₜ[R] x)) = _
  exact congrArg
    (fun f : baseTensor (R := R) (M.X p) (N.X q) ⟶ P.X ((p + q) + k) ↦
      f (m ⊗ₜ[R] x)) (ι_mapBifunctorDesc
        (K₁ := rightComplex M) (K₂ := leftComplex N) (F := baseBifunctor (R := R))
        (c := up ℤ)
        (fun a b h ↦ φ a b ≫ eqToHom (congrArg (fun t : ℤ ↦ P.X (t + k)) h))
        p q rfl)

/-- Two cochains of the same degree out of a relative tensor complex are equal when they agree
on every homogeneous pure tensor. -/
@[ext]
theorem gradedCochain_ext (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    {f g : Cochain (complex M N) P k}
    (h : ∀ (p q : ℤ) (m : M.X p) (x : N.X q),
      f.v (p + q) ((p + q) + k) rfl (tmul M N m x) =
        g.v (p + q) ((p + q) + k) rfl (tmul M N m x)) :
    f = g := by
  apply Cochain.ext
  intro n t hnt
  subst t
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  have heq :
      ModuleCat.ofHom ((f.v n (n + k) rfl).hom.comp (mk M N n)) =
        ModuleCat.ofHom ((g.v n (n + k) rfl).hom.comp (mk M N n)) := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    subst n
    exact h p q m x
  exact congrArg (fun t : rawTerm M N n ⟶ P.X (n + k) ↦ t.hom) heq

/-- A degree-`k` cochain agreeing with a balanced pairing on pure tensors is its canonical
lift. -/
theorem gradedLift_unique (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ)
    (f : Cochain (complex M N) P k)
    (h : ∀ (p q : ℤ) (m : M.X p) (x : N.X q),
      f.v (p + q) ((p + q) + k) rfl (tmul M N m x) = φ p q (m ⊗ₜ[R] x)) :
    f = gradedLift M N φ hφ := by
  apply gradedCochain_ext M N
  intro p q m x
  rw [gradedLift_tmul]
  exact h p q m x

private theorem gradedLift_v_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ)
    (p q n t : ℤ) (hn : p + q = n) (ht : n + k = t) (m : M.X p) (x : N.X q) :
    (gradedLift M N φ hφ).v n t ht
        (cast (congrArg (fun n : ℤ ↦ (family M N n : Type (max v w))) hn) (tmul M N m x)) =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
        (show (p + q) + k = t by omega)) (φ p q (m ⊗ₜ[R] x)) := by
  subst n
  subst t
  exact gradedLift_tmul M N φ hφ p q m x

private theorem delta_gradedLift_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ)
    (p q t : ℤ) (ht : ((p + q) + k) + 1 = t) (m : M.X p) (x : N.X q) :
    (δ k (k + 1) (gradedLift M N φ hφ)).v (p + q) t (by omega) (tmul M N m x) =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w))) ht)
        (P.d ((p + q) + k) (((p + q) + k) + 1) (φ p q (m ⊗ₜ[R] x)) -
          (k.negOnePow : R) •
            (cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
                (gradedDifferentialLeftDegree p q k))
                  (φ (p + 1) q (M.d p m ⊗ₜ[R] x)) +
              (p.negOnePow : R) •
                cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
                  (gradedDifferentialRightDegree p q k))
                    (φ p (q + 1) (m ⊗ₜ[R] N.d q x)))) := by
  subst t
  rw [δ_v k (k + 1) rfl _ (p + q) (((p + q) + k) + 1) (by omega)
    ((p + q) + k) ((p + q) + 1) (by omega) rfl]
  change P.d ((p + q) + k) (((p + q) + k) + 1)
      ((gradedLift M N φ hφ).v (p + q) ((p + q) + k) rfl (tmul M N m x)) +
    (k + 1).negOnePow •
      ((gradedLift M N φ hφ).v ((p + q) + 1) (((p + q) + k) + 1) (by omega)
        ((complex M N).d (p + q) ((p + q) + 1) (tmul M N m x))) = _
  rw [gradedLift_tmul, differential_tmul]
  erw [map_add, map_smul]
  erw [gradedLift_v_tmul M N φ hφ (p + 1) q ((p + q) + 1) (((p + q) + k) + 1)
      (differentialLeftDegree p q) (by omega),
    gradedLift_v_tmul M N φ hφ p (q + 1) ((p + q) + 1) (((p + q) + k) + 1)
      (differentialRightDegree p q) (by omega)]
  rw [Int.negOnePow_succ, Units.neg_smul]
  rw [sub_eq_add_neg]
  congr 1
  congr 1
  exact (Int.cast_smul_eq_zsmul R _ _).symm

/-- Differential compatibility of a balanced degree-`k` pairing is equivalent to its lifted
cochain being killed by the Hom-complex differential. -/
theorem gradedIsDifferentialCompatible_iff_delta_eq_zero
    (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ) :
    GradedIsDifferentialCompatible M N φ ↔
      δ k (k + 1) (gradedLift M N φ hφ) = 0 := by
  constructor
  · intro hd
    apply gradedCochain_ext M N
    intro p q m x
    rw [delta_gradedLift_tmul M N φ hφ p q _ (by omega), hd p q m x, sub_self]
    change cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w)))
      (show ((p + q) + k) + 1 = (p + q) + (k + 1) by omega)) 0 = 0
    have hz (i j : ℤ) (h : i = j) :
        cast (congrArg (fun n : ℤ ↦ (P.X n : Type (max v w))) h) (0 : P.X i) = 0 := by
      subst j
      rfl
    exact hz _ _ (by omega)
  · intro hd p q m x
    have hz := congrArg (fun z : Cochain (complex M N) P (k + 1) ↦
      z.v (p + q) (((p + q) + k) + 1) (by omega) (tmul M N m x)) hd
    rw [delta_gradedLift_tmul M N φ hφ p q _ rfl] at hz
    exact sub_eq_zero.mp hz

/-- A balanced differential-compatible degree-`k` pairing gives a degree-`k` cocycle in the
Hom complex out of the relative tensor product. -/
def gradedCocycleLift (M : DifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A)
    {P : CochainComplex (ModuleCat.{max v w} R) ℤ} {k : ℤ}
    (φ : GradedPairing M N P k) (hφ : GradedIsBalanced M N φ)
    (hd : GradedIsDifferentialCompatible M N φ) :
    Cocycle (complex M N) P k :=
  Cocycle.mk (gradedLift M N φ hφ) (k + 1) rfl
    ((gradedIsDifferentialCompatible_iff_delta_eq_zero M N φ hφ).mp hd)

end DifferentialGradedModule.TensorProduct
