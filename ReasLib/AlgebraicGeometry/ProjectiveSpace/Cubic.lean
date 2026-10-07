module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic

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
    coeff (Finsupp.single j 1) (linearCombination t i) = t j i :=
  sorry

/-- The pullback of `F` along `X i ↦ linearCombination t i`, i.e. the polynomial
`F(λ • t 0 + μ • t 1 + ν • t 2)` in `MvPolynomial (Fin 3) k`. -/
def restriction {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) :
    MvPolynomial (Fin 3) k :=
  aeval (linearCombination t) F

/-- Restriction sends the variable `X i` to the corresponding linear combination. -/
theorem restriction_X {k : Type u} [CommRing k] {n : ℕ}
    (t : Fin 3 → (Fin (n + 1) → k)) (i : Fin (n + 1)) :
    restriction (X i) t = linearCombination t i :=
  sorry

/-- Restriction is the identity on coefficients. -/
theorem restriction_C {k : Type u} [CommRing k] {n : ℕ} (a : k)
    (t : Fin 3 → (Fin (n + 1) → k)) : restriction (C a) t = C a :=
  sorry

/-- Restriction of a homogeneous cubic is a homogeneous cubic in three variables. -/
theorem restriction_isHomogeneous {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous 3)
    (t : Fin 3 → (Fin (n + 1) → k)) : (restriction F t).IsHomogeneous 3 :=
  sorry

/-- The polynomial restricted to the linear combinations of a triple is zero. -/
def SatisfiesStar {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) : Prop :=
  restriction F t = 0

/-- A triple satisfies the vanishing condition exactly when its restriction is zero. -/
theorem SatisfiesStar_iff {k : Type u} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (t : Fin 3 → (Fin (n + 1) → k)) :
    SatisfiesStar F t ↔ restriction F t = 0 :=
  sorry

/-- A homogeneous cubic restricts to zero exactly when all degree-three coefficients
of its restriction vanish. -/
theorem SatisfiesStar_iff_coeff {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous 3)
    (t : Fin 3 → (Fin (n + 1) → k)) :
    SatisfiesStar F t ↔
      ∀ d : Fin 3 →₀ ℕ, Finsupp.degree d = 3 → coeff d (restriction F t) = 0 :=
  sorry

/-- A polynomial with zero restriction evaluates to zero at every vector in the
span of the triple. -/
theorem eval_eq_zero_of_SatisfiesStar {k : Type u} [CommRing k] {n : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} {t : Fin 3 → (Fin (n + 1) → k)}
    (h : SatisfiesStar F t) {v : Fin (n + 1) → k}
    (hv : v ∈ Submodule.span k (Set.range t)) : eval v F = 0 :=
  sorry

/-- Three linearly independent vectors span a 3-dimensional linear subspace. -/
theorem finrank_span_eq_three_of_linearIndependent {k : Type u} [Field k] {n : ℕ}
    {t : Fin 3 → (Fin (n + 1) → k)} (ht : LinearIndependent k t) :
    Module.finrank k (Submodule.span k (Set.range t)) = 3 :=
  sorry

/-- The generic `3 × (n+1)` matrix of coordinate polynomials for a triple of vectors. -/
def coordMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin 3) (Fin (n + 1)) (MvPolynomial (Fin 3 × Fin (n + 1)) k) :=
  fun i j ↦ X (i, j)

/-- An entry of `coordMatrix k n` is the corresponding coordinate variable. -/
theorem coordMatrix_apply (k : Type u) [CommRing k] (n : ℕ)
    (i : Fin 3) (j : Fin (n + 1)) : coordMatrix k n i j = X (i, j) :=
  sorry

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
  sorry

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
  sorry

/-- Linear dependence of the residue rows is cut out by the 3-minors of
`coordMatrix k n`. -/
theorem dependentLocus_eq_zeroLocus (k : Type u) [CommRing k] (n : ℕ) :
    dependentLocus k n =
      zeroLocus (Matrix.minorIdeal 3 (coordMatrix k n) :
        Set (MvPolynomial (Fin 3 × Fin (n + 1)) k)) :=
  sorry

/-- For every coefficient ring, `dependentLocus k n` is Zariski closed. -/
theorem isClosed_dependentLocus (k : Type u) [CommRing k] (n : ℕ) :
    IsClosed (dependentLocus k n) :=
  sorry

/-- The topological Krull dimension of `dependentLocus k n` equals the Krull dimension of
the quotient by the 3-minors of `coordMatrix k n`. -/
theorem topologicalKrullDim_dependentLocus_eq_ringKrullDim
    (k : Type u) [CommRing k] (n : ℕ) :
    topologicalKrullDim (dependentLocus k n) =
      ringKrullDim
        (MvPolynomial (Fin 3 × Fin (n + 1)) k ⧸ Matrix.minorIdeal 3 (coordMatrix k n)) :=
  sorry

/-- The vector space of triples in `k^(n + 1)` has dimension `3 * (n + 1)`. -/
theorem finrank_triples {k : Type u} [Field k] (n : ℕ) :
    Module.finrank k (Fin 3 → (Fin (n + 1) → k)) = 3 * (n + 1) :=
  sorry

/-- The vector space of homogeneous cubics in three variables has dimension ten. -/
theorem finrank_homogeneousCubic {k : Type u} [Field k] :
    Module.finrank k (homogeneousSubmodule (Fin 3) k 3) = 10 :=
  sorry

/-- Subtracting the ten cubic coefficient equations from the dimension of the triple
space gives the expected dimension `3 * n - 7`. -/
theorem expectedDim_eq (n : ℕ) :
    (3 * (n + 1) : ℤ) - 10 = 3 * (n : ℤ) - 7 :=
  sorry

/-- For `1 ≤ n`, the locus of linearly dependent triples over a field has
topological Krull dimension `2 * n + 4`. -/
theorem topologicalKrullDim_dependentLocus {k : Type u} [Field k] {n : ℕ}
    (hn : 1 ≤ n) : topologicalKrullDim (dependentLocus k n) = 2 * n + 4 :=
  sorry

/-- The expected dimension of triples with zero cubic restriction exceeds the
dependent-locus dimension exactly when `12 ≤ n`. This dimension comparison does not
assert existence of an independent triple for every cubic. -/
theorem expectedDim_gt_dependentDim_iff {n : ℕ} :
    ((3 * (n + 1) : ℤ) - 10 > (2 * n + 4 : ℤ)) ↔ 12 ≤ n :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.Cubic
