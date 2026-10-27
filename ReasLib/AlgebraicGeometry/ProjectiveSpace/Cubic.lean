/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic
public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Linear substitutions of homogeneous cubics by three vectors

Given a cubic `F` on `k^{n+1}` and a triple `t` of vectors, the restriction
`F(λ • t 0 + μ • t 1 + ν • t 2)` is a polynomial in three variables.
Dependent triples are the rank-at-most-two locus of the generic `3 × (n+1)`
coordinate matrix.
-/

@[expose] public section

universe u

noncomputable section

open MvPolynomial PrimeSpectrum

namespace AlgebraicGeometry.ProjectiveSpace.Cubic

/-- The `i`-th coordinate of the linear combination `∑ j, C (t j i) * X j` in the
three variables `X 0, X 1, X 2`. -/
def linearCombination {k : Type u} [CommRing k] {n : ℕ}
    (t : Fin 3 → (Fin (n + 1) → k)) (i : Fin (n + 1)) : MvPolynomial (Fin 3) k :=
  Finset.univ.sum fun j : Fin 3 ↦ C (t j i) * X j

/-- The coefficient of `X j` in `linearCombination t i` is the coordinate `t j i`. -/
theorem linearCombination_apply {k : Type u} [CommRing k] {n : ℕ}
    (t : Fin 3 → (Fin (n + 1) → k)) (i : Fin (n + 1)) (j : Fin 3) :
    coeff (Finsupp.single j 1) (linearCombination t i) = t j i := by
  classical
  simp [linearCombination, coeff_sum, coeff_X, Finsupp.single_left_inj]

/-- The pullback of `F` along `X i ↦ linearCombination t i`, i.e. the polynomial
`F(λ • t 0 + μ • t 1 + ν • t 2)` in `MvPolynomial (Fin 3) k`. -/
def restriction {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) :
    MvPolynomial (Fin 3) k :=
  aeval (linearCombination t) F

/-- Restriction sends the variable `X i` to the corresponding linear combination. -/
theorem restriction_X {k : Type u} [CommRing k] {n : ℕ}
    (t : Fin 3 → (Fin (n + 1) → k)) (i : Fin (n + 1)) :
    restriction (X i) t = linearCombination t i := by
  exact aeval_X (linearCombination t) i

/-- Restriction is the identity on coefficients. -/
theorem restriction_C {k : Type u} [CommRing k] {n : ℕ} (a : k)
    (t : Fin 3 → (Fin (n + 1) → k)) : restriction (C a) t = C a := by
  exact aeval_C (linearCombination t) a

/-- Restriction of a homogeneous cubic is a homogeneous cubic in three variables. -/
theorem restriction_isHomogeneous {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous 3)
    (t : Fin 3 → (Fin (n + 1) → k)) : (restriction F t).IsHomogeneous 3 := by
  have hlinear (i : Fin (n + 1)) : (linearCombination t i).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ ↦ isHomogeneous_C_mul_X (t j i) j
  simpa only [restriction, one_mul] using hF.aeval (linearCombination t) hlinear

/-- The polynomial restricted to the linear combinations of a triple is zero. -/
def SatisfiesStar {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) : Prop :=
  restriction F t = 0

/-- A triple satisfies the vanishing condition exactly when its restriction is zero. -/
theorem SatisfiesStar_iff {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) :
    SatisfiesStar F t ↔ restriction F t = 0 :=
  Iff.rfl

/-- A homogeneous cubic restricts to zero exactly when all degree-three coefficients
of its restriction vanish. -/
theorem SatisfiesStar_iff_coeff {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous 3)
    (t : Fin 3 → (Fin (n + 1) → k)) :
    SatisfiesStar F t ↔
      ∀ d : Fin 3 →₀ ℕ, Finsupp.degree d = 3 → coeff d (restriction F t) = 0 := by
  constructor
  · intro h d _
    show coeff d (restriction F t) = 0
    rw [show restriction F t = 0 from h, coeff_zero]
  · intro h
    change restriction F t = 0
    ext d
    by_cases hd : Finsupp.degree d = 3
    · simpa using h d hd
    · simpa using (restriction_isHomogeneous hF t).coeff_eq_zero hd

/-- A polynomial with zero restriction evaluates to zero at every vector in the
span of the triple. -/
theorem eval_eq_zero_of_SatisfiesStar {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} {t : Fin 3 → (Fin (n + 1) → k)}
    (h : SatisfiesStar F t) {v : Fin (n + 1) → k}
    (hv : v ∈ Submodule.span k (Set.range t)) : eval v F = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hv
  have heval : (eval c ∘ linearCombination t) = v := by
    funext i
    simpa [linearCombination, eval_sum, Finset.sum_apply, smul_eq_mul, mul_comm]
      using congrFun hc i
  calc
    eval v F = eval (eval c ∘ linearCombination t) F := by rw [heval]
    _ = eval c (restriction F t) := eval_assoc (linearCombination t) c F
    _ = 0 := by rw [show restriction F t = 0 from h, map_zero]

/-- Three linearly independent vectors span a 3-dimensional linear subspace. -/
theorem finrank_span_eq_three_of_linearIndependent {k : Type u} [Field k] {n : ℕ}
    {t : Fin 3 → (Fin (n + 1) → k)} (ht : LinearIndependent k t) :
    Module.finrank k (Submodule.span k (Set.range t)) = 3 := by
  simpa using finrank_span_eq_card ht

/-- The generic `3 × (n+1)` matrix of coordinate polynomials for a triple of vectors. -/
def coordMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin 3) (Fin (n + 1)) (MvPolynomial (Fin 3 × Fin (n + 1)) k) :=
  fun i j ↦ X (i, j)

/-- An entry of `coordMatrix k n` is the corresponding coordinate variable. -/
theorem coordMatrix_apply (k : Type u) [CommRing k] (n : ℕ)
    (i : Fin 3) (j : Fin (n + 1)) : coordMatrix k n i j = X (i, j) :=
  rfl

/-- The image of `coordMatrix k n` in the residue field of a prime. -/
def residueMatrix {k : Type u} [CommRing k] {n : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin 3 × Fin (n + 1)) k)) :
    Matrix (Fin 3) (Fin (n + 1)) p.asIdeal.ResidueField :=
  (coordMatrix k n).map
    (algebraMap (MvPolynomial (Fin 3 × Fin (n + 1)) k) p.asIdeal.ResidueField)

/-- An entry of `residueMatrix p` is the residue of the corresponding matrix entry. -/
theorem residueMatrix_apply {k : Type u} [CommRing k] {n : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin 3 × Fin (n + 1)) k))
    (i : Fin 3) (j : Fin (n + 1)) :
    residueMatrix p i j =
      algebraMap (MvPolynomial (Fin 3 × Fin (n + 1)) k) p.asIdeal.ResidueField
        (coordMatrix k n i j) :=
  rfl

/-- The locus of primes at which the three residue rows of `coordMatrix k n` are
linearly dependent. -/
def dependentLocus (k : Type u) [CommRing k] (n : ℕ) :
    Set (PrimeSpectrum (MvPolynomial (Fin 3 × Fin (n + 1)) k)) :=
  {p | ¬ LinearIndependent p.asIdeal.ResidueField (residueMatrix p)}

/-- Membership in `dependentLocus k n` is linear dependence of the three residue rows. -/
theorem mem_dependentLocus_iff {k : Type u} [CommRing k] {n : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin 3 × Fin (n + 1)) k)) :
    p ∈ dependentLocus k n ↔
      ¬ LinearIndependent p.asIdeal.ResidueField (residueMatrix p) :=
  Iff.rfl

/-- Full row rank over a field is detected by a nonzero maximal minor. -/
private theorem linearIndependent_iff_exists_minor {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) :
    LinearIndependent K A ↔ ∃ e : Fin m ↪ Fin n, (A.submatrix id e).det ≠ 0 := by
  classical
  constructor
  · intro hA
    obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
    letI : Finite κ := Finite.of_injective a ha
    letI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = m := by
      rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_cols]
      simpa using hA.rank_matrix
    let e : Fin m ↪ Fin n :=
      (Fintype.equivFinOfCardEq hcard).symm.toEmbedding.trans ⟨a, ha⟩
    refine ⟨e, ?_⟩
    have hcol : LinearIndependent K (A.submatrix id e).col := by
      change LinearIndependent K ((A.col ∘ a) ∘ (Fintype.equivFinOfCardEq hcard).symm)
      exact hli.comp _ (Equiv.injective _)
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hcol)).ne_zero
  · rintro ⟨e, he⟩
    apply LinearIndependent.of_comp (LinearMap.funLeft K K e)
    exact Matrix.linearIndependent_rows_of_det_ne_zero he

/-- Linear dependence of the residue rows is cut out by the 3-minors of
`coordMatrix k n`. -/
theorem dependentLocus_eq_zeroLocus (k : Type u) [CommRing k] (n : ℕ) :
    dependentLocus k n =
      zeroLocus (Matrix.minorIdeal 3 (coordMatrix k n) :
        Set (MvPolynomial (Fin 3 × Fin (n + 1)) k)) := by
  classical
  ext p
  change (¬ LinearIndependent p.asIdeal.ResidueField (residueMatrix p)) ↔
    Matrix.minorIdeal 3 (coordMatrix k n) ≤ p.asIdeal
  rw [Matrix.minorIdeal, Ideal.span_le]
  constructor
  · intro hdep x hx
    rcases hx with ⟨⟨e₁, e₂⟩, rfl⟩
    apply Ideal.algebraMap_residueField_eq_zero.mp
    rw [RingHom.map_det]
    change ((residueMatrix p).submatrix e₁ e₂).det = 0
    let σ : Equiv.Perm (Fin 3) :=
      Equiv.ofBijective e₁ (Finite.injective_iff_bijective.mp e₁.injective)
    have hbase : ((residueMatrix p).submatrix id e₂).det = 0 := by
      by_contra hne
      exact hdep ((linearIndependent_iff_exists_minor _).mpr ⟨e₂, hne⟩)
    change (((residueMatrix p).submatrix id e₂).submatrix σ id).det = 0
    rw [Matrix.det_permute, hbase, mul_zero]
  · intro hspan hLI
    obtain ⟨e, he⟩ := (linearIndependent_iff_exists_minor _).mp hLI
    have hmem : ((coordMatrix k n).submatrix (Function.Embedding.refl _) e).det ∈
        p.asIdeal := hspan ⟨(Function.Embedding.refl _, e), rfl⟩
    have hzero := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [RingHom.map_det] at hzero
    exact he hzero

/-- For every coefficient ring, `dependentLocus k n` is Zariski closed. -/
theorem isClosed_dependentLocus (k : Type u) [CommRing k] (n : ℕ) :
    IsClosed (dependentLocus k n) := by
  rw [dependentLocus_eq_zeroLocus]
  exact isClosed_zeroLocus _

/-- The topological Krull dimension of `dependentLocus k n` equals the Krull dimension of
the quotient by the 3-minors of `coordMatrix k n`. -/
theorem topologicalKrullDim_dependentLocus_eq_ringKrullDim
    (k : Type u) [CommRing k] (n : ℕ) :
    topologicalKrullDim (dependentLocus k n) =
      ringKrullDim
        (MvPolynomial (Fin 3 × Fin (n + 1)) k ⧸ Matrix.minorIdeal 3 (coordMatrix k n)) := by
  rw [dependentLocus_eq_zeroLocus]
  exact Ideal.topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient _

/-- The vector space of triples in `k^(n + 1)` has dimension `3 * (n + 1)`. -/
theorem finrank_triples {k : Type u} [Field k] (n : ℕ) :
    Module.finrank k (Fin 3 → (Fin (n + 1) → k)) = 3 * (n + 1) := by
  simp [Module.finrank_pi_fintype]

/-- The vector space of homogeneous cubics in three variables has dimension ten. -/
theorem finrank_homogeneousCubic {k : Type u} [Field k] :
    Module.finrank k (homogeneousSubmodule (Fin 3) k 3) = 10 := by
  classical
  rw [← weightedHomogeneousSubmodule_one,
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let S : Set (Fin 3 →₀ ℕ) := {d | Finsupp.weight (1 : Fin 3 → ℕ) d = 3}
  letI : Fintype S := (Finsupp.finite_of_nat_weight_eq (1 : Fin 3 → ℕ)
    (fun _ ↦ by simp) 3).fintype
  change Module.finrank k (restrictSupport k S) = 10
  rw [Module.finrank_eq_card_basis (basisRestrictSupport k S)]
  let e : Sym (Fin 3) 3 ≃ S := (Sym.equivNatSum (Fin 3) 3).trans
    (Equiv.subtypeEquivRight fun d ↦ by
      change Finsupp.degree d = 3 ↔ Finsupp.weight (fun _ : Fin 3 ↦ 1) d = 3
      rw [Finsupp.degree_eq_weight_one])
  rw [← Fintype.card_congr e, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  norm_num [Nat.multichoose_eq, Nat.choose]

/-- Subtracting the ten cubic coefficient equations from the dimension of the triple
space gives the expected dimension `3 * n - 7`. -/
theorem expectedDim_eq (n : ℕ) :
    (3 * (n + 1) : ℤ) - 10 = 3 * (n : ℤ) - 7 := by
  ring

/-- For `1 ≤ n`, the locus of linearly dependent triples over a field has
topological Krull dimension `2 * n + 4`. -/
theorem topologicalKrullDim_dependentLocus {k : Type u} [Field k] {n : ℕ}
    (hn : 1 ≤ n) : topologicalKrullDim (dependentLocus k n) = 2 * n + 4 :=
  sorry

/-- The expected dimension of triples with zero cubic restriction exceeds the
dependent-locus dimension exactly when `12 ≤ n`. This dimension comparison does not
assert existence of an independent triple for every cubic. -/
theorem expectedDim_gt_dependentDim_iff {n : ℕ} :
    ((3 * (n + 1) : ℤ) - 10 > (2 * n + 4 : ℤ)) ↔ 12 ≤ n := by
  constructor
  · intro h
    have hn : (12 : ℤ) ≤ n := by linarith
    exact_mod_cast hn
  · intro h
    have hn : (12 : ℤ) ≤ n := by exact_mod_cast h
    linarith

end AlgebraicGeometry.ProjectiveSpace.Cubic
