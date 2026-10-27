/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower.Coordinates
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Coincidence divisors

The product of partial diagonal ideals cuts out the locus where the first
coordinate agrees with at least one later coordinate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The `i`-th partial diagonal on `tensorPower X (r + 1)`, cut out by `x = x_{i+1}`. -/
noncomputable def partialDiagonal (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    (tensorPower X (r + 1)).left.IdealSheafData :=
  (pullback.diagonal X.hom).ker.comap (pairCoord X r i).left

/-- The partial diagonal is the inverse image of the diagonal ideal. -/
theorem partialDiagonal_eq (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    partialDiagonal X r i =
      (pullback.diagonal X.hom).ker.comap (pairCoord X r i).left :=
  rfl

/-- The coincidence divisor on `tensorPower X (r + 1)` is the product of the partial diagonals. -/
noncomputable def coincidenceDivisor (X : SchemeOverField k) (r : ℕ) :
    (tensorPower X (r + 1)).left.IdealSheafData :=
  (Finset.univ : Finset (Fin r)).prod (partialDiagonal X r)

/-- The coincidence divisor is the product of the partial diagonal ideals. -/
theorem coincidenceDivisor_eq (X : SchemeOverField k) (r : ℕ) :
    coincidenceDivisor X r =
      (Finset.univ : Finset (Fin r)).prod (partialDiagonal X r) :=
  rfl

/-- The support of the coincidence divisor is the union of the partial-diagonal supports. -/
theorem support_coincidenceDivisor (X : SchemeOverField k) (r : ℕ) :
    (coincidenceDivisor X r).support =
      (Finset.univ : Finset (Fin r)).sup fun i ↦ (partialDiagonal X r i).support := by
  classical
  have h (s : Finset (Fin r)) :
      (s.prod (partialDiagonal X r)).support =
        s.sup (fun i ↦ (partialDiagonal X r i).support) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty, Finset.sup_empty,
          Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul, ih, Finset.sup_insert]
  exact h Finset.univ

/-- In degree one, the coincidence divisor is the inverse image of the diagonal along the
canonical pair of coordinates `tensorPower X 2 ⟶ X ⊗ X`. -/
theorem coincidenceDivisor_one (X : SchemeOverField k) :
    coincidenceDivisor X 1 =
      (pullback.diagonal X.hom).ker.comap (pairCoord X 1 0).left := by
  simp [coincidenceDivisor, partialDiagonal]

/-- A closed point of `tensorPower X (r + 1)` lies on the coincidence divisor if and only if
the first coordinate equals some later coordinate. -/
theorem mem_support_coincidenceDivisor_closedPoints_iff
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] (r : ℕ)
    {z : (tensorPower X (r + 1)).left}
    (hz : z ∈ closedPoints (tensorPower X (r + 1)).left) :
    z ∈ (coincidenceDivisor X r).support ↔
      ∃ i : Fin r,
        (coord X (r + 1) 0).left.base z = (coord X (r + 1) i.succ).left.base z := by
  classical
  have hft (n : ℕ) : LocallyOfFiniteType (tensorPower X n).hom := by
    induction n with
    | zero =>
        change LocallyOfFiniteType (𝟙 (Spec (.of k)))
        infer_instance
    | succ n ih =>
        letI := ih
        change LocallyOfFiniteType (pullback.fst X.hom (tensorPower X n).hom ≫ X.hom)
        infer_instance
  letI := hft (r + 1)
  have hmem : z ∈ (coincidenceDivisor X r).support ↔
      ∃ i : Fin r, z ∈ (partialDiagonal X r i).support := by
    rw [support_coincidenceDivisor]
    change z ∈ ((Finset.univ.sup (fun i : Fin r ↦ (partialDiagonal X r i).support) :
      TopologicalSpace.Closeds (tensorPower X (r + 1)).left) : Set _) ↔ _
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const, Function.comp_apply]
    rfl
  rw [hmem]
  apply exists_congr
  intro i
  let q : (tensorPower X (r + 1)).left ⟶ pullback X.hom X.hom :=
    (pairCoord X r i).left
  have hfst : q ≫ pullback.fst X.hom X.hom =
      (coord X (r + 1) 0).left := by
    simp [q, pairCoord, pullback.lift_fst]
  have hsnd : q ≫ pullback.snd X.hom X.hom =
      (coord X (r + 1) i.succ).left := by
    simp [q, pairCoord, pullback.lift_snd]
  have hdiag : (pullback.diagonal X.hom).ker.supportSet =
      Set.range (pullback.diagonal X.hom) := by
    exact (Scheme.Hom.support_ker _).trans
      (pullback.diagonal X.hom).isClosedEmbedding.isClosed_range.closure_eq
  rw [partialDiagonal, Scheme.IdealSheafData.support_comap]
  change q z ∈ (pullback.diagonal X.hom).ker.supportSet ↔ _
  rw [hdiag]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 := congrArg (pullback.fst X.hom X.hom) hx
    have hx1 := congrArg (pullback.snd X.hom X.hom) hx
    change (pullback.diagonal X.hom ≫ pullback.fst X.hom X.hom) x =
      (q ≫ pullback.fst X.hom X.hom) z at hx0
    change (pullback.diagonal X.hom ≫ pullback.snd X.hom X.hom) x =
      (q ≫ pullback.snd X.hom X.hom) z at hx1
    rw [pullback.diagonal_fst, hfst] at hx0
    rw [pullback.diagonal_snd, hsnd] at hx1
    exact hx0.symm.trans hx1
  · intro h
    let p := pointOfClosedPoint (tensorPower X (r + 1)).hom z hz
    let a := p ≫ (coord X (r + 1) 0).left
    let b := p ≫ (coord X (r + 1) i.succ).left
    have hab : a = b := by
      apply ext_of_apply_closedPoint_eq X.hom
      · dsimp only [a]
        rw [Category.assoc, Over.w]
        exact pointOfClosedPoint_comp _ _ _
      · dsimp only [b]
        rw [Category.assoc, Over.w]
        exact pointOfClosedPoint_comp _ _ _
      · simpa only [a, b, Scheme.Hom.comp_apply, p, pointOfClosedPoint_apply] using h
    have hlift : a ≫ pullback.diagonal X.hom = p ≫ q := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id,
          Category.assoc, hfst]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id,
          Category.assoc, hsnd, hab]
    refine ⟨a (IsLocalRing.closedPoint k), ?_⟩
    change (a ≫ pullback.diagonal X.hom) (IsLocalRing.closedPoint k) =
      q z
    rw [hlift, Scheme.Hom.comp_apply]
    congr 1
    exact pointOfClosedPoint_apply _ _ _ _

/-- The diagonal of a smooth curve over an algebraically closed field is an effective
Cartier divisor. -/
instance instIsEffectiveCartierDivisor_diagonal
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] :
    IsEffectiveCartierDivisor (pullback.diagonal X.hom) :=
  sorry

/-- Each partial diagonal of a smooth curve over an algebraically closed field is an
effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_partialDiagonal
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) (i : Fin r) :
    IsEffectiveCartierDivisor (partialDiagonal X r i).subschemeι :=
  sorry

/-- The coincidence divisor on every tensor power of a smooth curve over an algebraically
closed field is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_coincidenceDivisor
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) :
    IsEffectiveCartierDivisor (coincidenceDivisor X r).subschemeι :=
  sorry

/-- For a positive tensor-power degree, the coincidence locus of a smooth curve over an
algebraically closed field defines an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_coincidenceDivisor
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] (r : ℕ) (hr : 1 ≤ r) :
    IsEffectiveCartierDivisor (coincidenceDivisor X r).subschemeι := by
  infer_instance

/-- The ideal sheaf of the coincidence divisor is invertible. -/
theorem coincidenceDivisor_invertibleIdealSheaf
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) :
    Scheme.Modules.Invertible
      (RingedSpace.Hom.idealSheaf (coincidenceDivisor X r).subschemeι.toShHom) :=
  IsEffectiveCartierDivisor.invertibleIdealSheaf

end AlgebraicGeometry.SchemeOverField
