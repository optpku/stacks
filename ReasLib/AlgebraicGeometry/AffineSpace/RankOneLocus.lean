/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

/-!
# Rank-one matrices as a locally closed subset of affine 9-space

This file records the set `V_0` of `3 × 3` rank-one matrices over a field `k`,
the identification `Mat(3 × 3, k) = k^9` via `finProdFinEquiv`, and the Zariski
locally closed rank-exactly-one locus `V` in `AffineSpaceOverField k 9`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AffineSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The set of `3 × 3` matrices of rank exactly `1` over `k`. -/
def rankOneMatrices (k : Type u) [Field k] : Set (Matrix (Fin 3) (Fin 3) k) :=
  {A | A.rank = 1}

/-- Membership in `rankOneMatrices` is the condition `Matrix.rank A = 1`. -/
theorem mem_rankOneMatrices_iff (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) :
    A ∈ rankOneMatrices k ↔ A.rank = 1 := Iff.rfl

/-- Flatten a `3 × 3` matrix to a coordinate `9`-tuple along `finProdFinEquiv`. -/
def coordsOfMatrix (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) : Fin 9 → k :=
  fun t ↦
    let indices := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm t
    A indices.1 indices.2

/-- Rebuild a `3 × 3` matrix from a coordinate `9`-tuple along `finProdFinEquiv`. -/
def matrixOfCoords (k : Type u) [Field k] (a : Fin 9 → k) : Matrix (Fin 3) (Fin 3) k :=
  .of fun i j ↦ a (finProdFinEquiv (i, j))

/-- `coordsOfMatrix` is a left inverse of `matrixOfCoords`. -/
theorem coordsOfMatrix_matrixOfCoords (k : Type u) [Field k] (a : Fin 9 → k) :
    coordsOfMatrix k (matrixOfCoords k a) = a := by
  funext t
  simp [coordsOfMatrix, matrixOfCoords]

/-- `matrixOfCoords` is a left inverse of `coordsOfMatrix`. -/
theorem matrixOfCoords_coordsOfMatrix (k : Type u) [Field k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    matrixOfCoords k (coordsOfMatrix k A) = A := by
  ext i j
  simp [matrixOfCoords, coordsOfMatrix]

/-- The generic `3 × 3` matrix of standard affine coordinates on
`AffineSpaceOverField k 9`, indexed by `finProdFinEquiv`. -/
def genericMatrix (k : Type u) [Field k] :
    Matrix (Fin 3) (Fin 3) Γ(AffineSpaceOverField k 9, ⊤) :=
  .of fun i j ↦ coord (Spec (CommRingCat.of.{u} k)) (ULift.up (finProdFinEquiv (i, j)))

/-- An entry of `genericMatrix` is the corresponding affine coordinate. -/
theorem genericMatrix_apply (k : Type u) [Field k] (i j : Fin 3) :
    genericMatrix k i j =
      coord (Spec (CommRingCat.of.{u} k)) (ULift.up (finProdFinEquiv (i, j))) := rfl

/-- The set of complementary `2 × 2` minors of `genericMatrix`. -/
def twoMinors (k : Type u) [Field k] : Set Γ(AffineSpaceOverField k 9, ⊤) :=
  Set.range fun p : Fin 3 × Fin 3 ↦
    ((genericMatrix k).submatrix p.1.succAbove p.2.succAbove).det

/-- The closed rank-at-most-one locus in `AffineSpaceOverField k 9`, cut out by
the vanishing of all complementary `2 × 2` minors. -/
def rankLeOneLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  (AffineSpaceOverField k 9).zeroLocus (twoMinors k)

/-- The origin in `AffineSpaceOverField k 9`, cut out by the nine affine
coordinates. -/
def rankZeroLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  (AffineSpaceOverField k 9).zeroLocus (Set.range (coord (Spec (CommRingCat.of.{u} k))))

/-- The rank-exactly-one locus in `AffineSpaceOverField k 9`. -/
def rankOneLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  rankLeOneLocus k \ rankZeroLocus k

/-- The rank-at-most-one locus is Zariski closed. -/
theorem isClosed_rankLeOneLocus (k : Type u) [Field k] :
    IsClosed (rankLeOneLocus k) :=
  (AffineSpaceOverField k 9).zeroLocus_isClosed (twoMinors k)

/-- The origin in `AffineSpaceOverField k 9` is Zariski closed. -/
theorem isClosed_rankZeroLocus (k : Type u) [Field k] :
    IsClosed (rankZeroLocus k) :=
  (AffineSpaceOverField k 9).zeroLocus_isClosed _

/-- The rank-exactly-one locus is Zariski locally closed. -/
theorem isLocallyClosed_rankOneLocus (k : Type u) [Field k] :
    IsLocallyClosed (rankOneLocus k) := by
  refine ⟨(rankZeroLocus k)ᶜ, rankLeOneLocus k,
    (isClosed_rankZeroLocus k).isOpen_compl, isClosed_rankLeOneLocus k, ?_⟩
  ext x
  exact and_comm

/-- The morphism `Spec k ⟶ AffineSpaceOverField k 9` with affine coordinates `a`. -/
def homOfCoords (k : Type u) [Field k] (a : Fin 9 → k) :
    Spec (CommRingCat.of.{u} k) ⟶ AffineSpaceOverField k 9 :=
  homOfVector (𝟙 _) fun i ↦ (Scheme.ΓSpecIso (CommRingCat.of.{u} k)).inv (a i.down)

/-- A coordinate morphism `homOfCoords a` lies over `Spec k`. -/
theorem homOfCoords_comp (k : Type u) [Field k] (a : Fin 9 → k) :
    homOfCoords k a ≫ affineSpaceOverFieldHom k 9 = 𝟙 _ :=
  homOfVector_over _ _

/-- The closed point of `AffineSpaceOverField k 9` associated to a `3 × 3` matrix. -/
def closedPointOfMatrix (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) :
    AffineSpaceOverField k 9 :=
  homOfCoords k (coordsOfMatrix k A) (IsLocalRing.closedPoint k)

/-- The image of a matrix under `closedPointOfMatrix` is a closed point. -/
theorem isClosed_singleton_closedPointOfMatrix (k : Type u) [Field k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    IsClosed {closedPointOfMatrix k A} := by
  letI : IsClosedImmersion (homOfCoords k (coordsOfMatrix k A)) :=
    isClosedImmersion_of_comp_eq_id _ _ (homOfCoords_comp k (coordsOfMatrix k A))
  have h := (homOfCoords k (coordsOfMatrix k A)).isClosedEmbedding.isClosed_range
  rwa [Set.range_eq_singleton] at h
  exact fun x ↦ congrArg (homOfCoords k (coordsOfMatrix k A))
    (Subsingleton.elim x (IsLocalRing.closedPoint k))

/-- Read a closed point of `AffineSpaceOverField k 9` as a `3 × 3` matrix over `k`. -/
def matrixOfClosedPoint (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    Matrix (Fin 3) (Fin 3) k :=
  matrixOfCoords k fun t ↦
    (Scheme.ΓSpecIso (CommRingCat.of.{u} k)).hom
      ((pointOfClosedPoint (affineSpaceOverFieldHom k 9) x hx).appTop
        (coord (Spec (CommRingCat.of.{u} k)) (ULift.up t)))

/-- `matrixOfClosedPoint` recovers a matrix from its associated closed point. -/
theorem matrixOfClosedPoint_closedPointOfMatrix (k : Type u) [Field k] [IsAlgClosed k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    matrixOfClosedPoint k (isClosed_singleton_closedPointOfMatrix k A) = A := by
  have hpoint : pointOfClosedPoint (affineSpaceOverFieldHom k 9)
      (closedPointOfMatrix k A) (isClosed_singleton_closedPointOfMatrix k A) =
      homOfCoords k (coordsOfMatrix k A) := by
    apply ext_of_apply_closedPoint_eq (affineSpaceOverFieldHom k 9)
    · exact pointOfClosedPoint_comp _ _ _
    · exact homOfCoords_comp k _
    · simp only [pointOfClosedPoint_apply, closedPointOfMatrix]
  unfold matrixOfClosedPoint
  rw [hpoint]
  simpa [homOfCoords] using matrixOfCoords_coordsOfMatrix k A

/-- `closedPointOfMatrix` recovers a closed point from its associated matrix. -/
theorem closedPointOfMatrix_matrixOfClosedPoint (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    closedPointOfMatrix k (matrixOfClosedPoint k hx) = x := by
  have hpoint : homOfCoords k (coordsOfMatrix k (matrixOfClosedPoint k hx)) =
      pointOfClosedPoint (affineSpaceOverFieldHom k 9) x hx := by
    apply hom_ext
    · rw [homOfCoords_comp, pointOfClosedPoint_comp]
    · intro i
      simp [homOfCoords, matrixOfClosedPoint, coordsOfMatrix_matrixOfCoords]
  unfold closedPointOfMatrix
  rw [hpoint]
  exact pointOfClosedPoint_apply _ _ _ _

private lemma rank_eq_one_iff_nonzero_and_minors (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) :
    A.rank = 1 ↔ A ≠ 0 ∧ ∀ p q : Fin 3, (A.submatrix p.succAbove q.succAbove).det = 0 := by
  classical
  constructor
  · intro hA
    refine ⟨?_, ?_⟩
    · rintro rfl
      simpa using hA
    · intro p q
      have hr := Matrix.rank_submatrix_le A p.succAbove q.succAbove
      rw [hA] at hr
      by_contra hd
      have hu := Matrix.rank_of_isUnit (A.submatrix p.succAbove q.succAbove)
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
      simp only [Fintype.card_fin] at hu
      omega
  · rintro ⟨hA, hmin⟩
    obtain ⟨i₀, j₀, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (by ext i j; exact h i j)
    -- Every pair of distinct rows and columns occurs in a complementary minor.
    have hcross (i i' j j' : Fin 3) : A i j * A i' j' = A i j' * A i' j := by
      have h00 := hmin 0 0
      have h01 := hmin 0 1
      have h02 := hmin 0 2
      have h10 := hmin 1 0
      have h11 := hmin 1 1
      have h12 := hmin 1 2
      have h20 := hmin 2 0
      have h21 := hmin 2 1
      have h22 := hmin 2 2
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, sub_eq_zero] at h00 h01 h02 h10 h11 h12 h20 h21 h22
      change A 1 1 * A 2 2 = A 1 2 * A 2 1 at h00
      change A 1 0 * A 2 2 = A 1 2 * A 2 0 at h01
      change A 1 0 * A 2 1 = A 1 1 * A 2 0 at h02
      change A 0 1 * A 2 2 = A 0 2 * A 2 1 at h10
      change A 0 0 * A 2 2 = A 0 2 * A 2 0 at h11
      change A 0 0 * A 2 1 = A 0 1 * A 2 0 at h12
      change A 0 1 * A 1 2 = A 0 2 * A 1 1 at h20
      change A 0 0 * A 1 2 = A 0 2 * A 1 0 at h21
      change A 0 0 * A 1 1 = A 0 1 * A 1 0 at h22
      clear hmin hA hij
      fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
        simp_all only [Fin.isValue, mul_comm, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta] <;>
        first
        | exact (mul_comm _ _).trans (h22.trans (mul_comm _ _))
        | exact (mul_comm _ _).trans (h22.symm.trans (mul_comm _ _))
    have hfactor : A = Matrix.vecMulVec (fun i ↦ A i j₀) (fun j ↦ A i₀ j / A i₀ j₀) := by
      ext i j
      change A i j = A i j₀ * (A i₀ j / A i₀ j₀)
      rw [← mul_div_assoc]
      exact (eq_div_iff hij).mpr (hcross i i₀ j j₀)
    have hle : A.rank ≤ 1 := by
      rw [hfactor]
      exact Matrix.rank_vecMulVec_le _ _
    have hne : A.rank ≠ 0 := by
      intro hz
      have hs : Submodule.span k (Set.range A.col) = ⊥ :=
        Submodule.finrank_eq_zero.mp ((Matrix.rank_eq_finrank_span_cols A).symm.trans hz)
      have hc : A.col j₀ ∈ Submodule.span k (Set.range A.col) :=
        Submodule.subset_span ⟨j₀, rfl⟩
      rw [hs, Submodule.mem_bot] at hc
      exact hij (congrFun hc i₀)
    omega

private lemma mem_zeroLocus_point_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (p : Spec (CommRingCat.of k) ⟶ X) (s : Set Γ(X, ⊤)) :
    p (IsLocalRing.closedPoint k) ∈ X.zeroLocus s ↔
      ∀ f ∈ s, (Scheme.ΓSpecIso (CommRingCat.of k)).hom (p.appTop f) = 0 := by
  classical
  rw [Scheme.mem_zeroLocus_iff]
  have hp (f : Γ(X, ⊤)) : p (IsLocalRing.closedPoint k) ∈ X.basicOpen f ↔
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom (p.appTop f) ≠ 0 := by
    change IsLocalRing.closedPoint k ∈ p ⁻¹ᵁ X.basicOpen f ↔ _
    rw [Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine']
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom (p.appTop f) ∉
      IsLocalRing.maximalIdeal k ↔ _
    simp only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  simp only [hp, not_not]

/-- A closed point of `AffineSpaceOverField k 9` lies in `rankOneLocus` if and only
if the associated matrix has rank `1`. -/
theorem mem_rankOneLocus_closedPoint_iff (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    x ∈ rankOneLocus k ↔ (matrixOfClosedPoint k hx).rank = 1 := by
  let p := pointOfClosedPoint (affineSpaceOverFieldHom k 9) x hx
  let e : Γ(AffineSpaceOverField k 9, ⊤) →+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp p.appTop.hom
  let A := matrixOfClosedPoint k hx
  have hdet (i j : Fin 3) :
      e (((genericMatrix k).submatrix i.succAbove j.succAbove).det) =
        (A.submatrix i.succAbove j.succAbove).det := by
    rw [e.map_det]
    congr 1
  have hle : x ∈ rankLeOneLocus k ↔
      ∀ i j : Fin 3, (A.submatrix i.succAbove j.succAbove).det = 0 := by
    have h := mem_zeroLocus_point_iff k p (twoMinors k)
    dsimp only [p] at h
    rw [pointOfClosedPoint_apply] at h
    change x ∈ rankLeOneLocus k ↔ ∀ f ∈ twoMinors k, e f = 0 at h
    simpa only [twoMinors, Set.forall_mem_range, Prod.forall, hdet] using h
  have hz : x ∈ rankZeroLocus k ↔ A = 0 := by
    have h := mem_zeroLocus_point_iff k p
      (Set.range (coord (Spec (CommRingCat.of k))))
    dsimp only [p] at h
    rw [pointOfClosedPoint_apply] at h
    change x ∈ rankZeroLocus k ↔
      ∀ f ∈ Set.range (coord (Spec (CommRingCat.of k))), e f = 0 at h
    rw [h]
    simp only [Set.forall_mem_range]
    constructor
    · intro hc
      ext i j
      exact hc (ULift.up (finProdFinEquiv (i, j)))
    · intro hA t
      have hcoord : e (coord (Spec (CommRingCat.of k)) t) = coordsOfMatrix k A t.down := by
        change e (coord (Spec (CommRingCat.of k)) t) =
          coordsOfMatrix k (matrixOfCoords k (fun t ↦
            e (coord (Spec (CommRingCat.of k)) (ULift.up t)))) t.down
        rw [coordsOfMatrix_matrixOfCoords]
      rw [hcoord, hA]
      rfl
  change x ∈ rankLeOneLocus k ∧ x ∉ rankZeroLocus k ↔ A.rank = 1
  rw [hle, hz, rank_eq_one_iff_nonzero_and_minors]
  exact and_comm

/-- Over an algebraically closed field, the closed points of the rank-one locus
are exactly the points represented by rank-one matrices. -/
theorem closedPoints_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    rankOneLocus k ∩ closedPoints (AffineSpaceOverField k 9) =
      closedPointOfMatrix k '' rankOneMatrices k := by
  ext x
  constructor
  · rintro ⟨hx, hclosed⟩
    exact ⟨matrixOfClosedPoint k hclosed,
      (mem_rankOneLocus_closedPoint_iff k hclosed).mp hx,
      closedPointOfMatrix_matrixOfClosedPoint k hclosed⟩
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, isClosed_singleton_closedPointOfMatrix k A⟩
    apply (mem_rankOneLocus_closedPoint_iff k
      (isClosed_singleton_closedPointOfMatrix k A)).mpr
    rw [matrixOfClosedPoint_closedPointOfMatrix]
    exact hA

/-- The rank-exactly-one locus in affine `9`-space over an algebraically closed
field is irreducible. -/
theorem isIrreducible_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    IsIrreducible (rankOneLocus k) := sorry

/-- The rank-exactly-one locus in affine `9`-space over an algebraically closed
field has topological Krull dimension `5`. -/
theorem topologicalKrullDim_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    topologicalKrullDim (rankOneLocus k : Set (AffineSpaceOverField k 9)) = (5 : WithBot ℕ∞) := sorry

end AlgebraicGeometry.AffineSpace
