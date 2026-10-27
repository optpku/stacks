/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

universe u

noncomputable section

namespace ZeroDimEpi

open MvPolynomial
open scoped TensorProduct

/-- The two families of source variables `x i` and `z i` for `i ≥ 1`. -/
inductive SrcVar
  | x : ℕ+ → SrcVar
  | z : ℕ+ → SrcVar
  deriving DecidableEq

/-- The two families of target variables `x i` and `y i` for `i ≥ 1`. -/
inductive TgtVar
  | x : ℕ+ → TgtVar
  | y : ℕ+ → TgtVar
  deriving DecidableEq

/-- The source ℤ-grading of variables, with `deg x i = -1` and `deg z i = 0`. -/
def srcDeg : SrcVar → ℤ
  | .x _ => -1
  | .z _ => 0

/-- The target ℤ-grading of variables, with `deg x i = -1` and `deg y i = 1`. -/
def tgtDeg : TgtVar → ℤ
  | .x _ => -1
  | .y _ => 1

variable (k : Type u)

section

variable [CommRing k]

/-- The source relation `X i ^ (4 ^ i)`. -/
def srcXPow (i : ℕ+) : MvPolynomial SrcVar k :=
  X (.x i) ^ (4 ^ (i : ℕ))

/-- The source relation `Z i ^ (4 ^ i)`. -/
def srcZPow (i : ℕ+) : MvPolynomial SrcVar k :=
  X (.z i) ^ (4 ^ (i : ℕ))

/-- The target relation `X i ^ (4 ^ i)`. -/
def tgtXPow (i : ℕ+) : MvPolynomial TgtVar k :=
  X (.x i) ^ (4 ^ (i : ℕ))

/-- The target relation `Y i - X (i + 1) * Y (i + 1) ^ 2`. -/
def tgtYRecurrence (i : ℕ+) : MvPolynomial TgtVar k :=
  X (.y i) - X (.x (i + 1)) * X (.y (i + 1)) ^ 2

/-- The defining ideal `(x i ^ (4 ^ i), z i ^ (4 ^ i))` of the source presentation. -/
def srcIdeal : Ideal (MvPolynomial SrcVar k) :=
  Ideal.span (Set.range (srcXPow k) ∪ Set.range (srcZPow k))

/-- The defining ideal `(x i ^ (4 ^ i), y i - x (i + 1) y (i + 1) ^ 2)` of the target
presentation. -/
def tgtIdeal : Ideal (MvPolynomial TgtVar k) :=
  Ideal.span (Set.range (tgtXPow k) ∪ Set.range (tgtYRecurrence k))

/-- The source ring `k[x i, z i] ⧸ (x i ^ (4 ^ i), z i ^ (4 ^ i))`. -/
abbrev Src : Type u := MvPolynomial SrcVar k ⧸ srcIdeal k

/-- The target ring `k[x i, y i] ⧸ (x i ^ (4 ^ i), y i - x (i + 1) y (i + 1) ^ 2)`. -/
abbrev Tgt : Type u := MvPolynomial TgtVar k ⧸ tgtIdeal k

/-- The image of `x i` in the source quotient. -/
def srcX (i : ℕ+) : Src k :=
  Ideal.Quotient.mk (srcIdeal k) (X (.x i))

/-- The image of `z i` in the source quotient. -/
def srcZ (i : ℕ+) : Src k :=
  Ideal.Quotient.mk (srcIdeal k) (X (.z i))

/-- The image of `x i` in the target quotient. -/
def tgtX (i : ℕ+) : Tgt k :=
  Ideal.Quotient.mk (tgtIdeal k) (X (.x i))

/-- The image of `y i` in the target quotient. -/
def tgtY (i : ℕ+) : Tgt k :=
  Ideal.Quotient.mk (tgtIdeal k) (X (.y i))

/-- The polynomial-level comparison sending `x i` to `x i` and `z i` to `x i * y i`. -/
def srcToTgt : MvPolynomial SrcVar k →ₐ[k] MvPolynomial TgtVar k :=
  aeval fun v ↦
    match v with
    | .x i => X (TgtVar.x i)
    | .z i => X (TgtVar.x i) * X (TgtVar.y i)

/-- The source relations vanish after the comparison map into the target quotient. -/
theorem srcToTgt_mem :
    ∀ p ∈ srcIdeal k, ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom) p = 0 := by
  suffices srcIdeal k ≤ RingHom.ker
      ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom) from
    fun p hp ↦ this hp
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · change ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom)
        (srcXPow k i) = 0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      srcXPow, srcToTgt, map_pow, aeval_X]
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
  · change ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom)
        (srcZPow k i) = 0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      srcZPow, srcToTgt, map_pow, aeval_X, mul_pow, map_mul]
    have hx : Ideal.Quotient.mk (tgtIdeal k)
        ((X (TgtVar.x i) : MvPolynomial TgtVar k) ^ (4 ^ (i : ℕ))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
    rw [map_pow] at hx
    rw [hx, zero_mul]

/-- The induced homomorphism of presentations. -/
def hom : Src k →+* Tgt k :=
  Ideal.Quotient.lift (srcIdeal k) ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom)
    (srcToTgt_mem k)

/-- The canonical `Src`-algebra structure on `Tgt` induced by `hom`. -/
instance instAlgebra : Algebra (Src k) (Tgt k) :=
  (hom k).toAlgebra

/-- The comparison map sends `srcX i` to `tgtX i`. -/
theorem hom_srcX (i : ℕ+) : hom k (srcX k i) = tgtX k i := by
  simp [hom, srcX, tgtX, srcToTgt]

/-- The comparison map sends `srcZ i` to `tgtX i * tgtY i`. -/
theorem hom_srcZ (i : ℕ+) : hom k (srcZ k i) = tgtX k i * tgtY k i := by
  simp [hom, srcZ, tgtX, tgtY, srcToTgt]

/-- The source generators `srcX i` are nilpotent of index `4 ^ i`. -/
theorem srcX_pow_eq_zero (i : ℕ+) : srcX k i ^ (4 ^ (i : ℕ)) = 0 := by
  rw [srcX, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inl ⟨i, rfl⟩))

/-- The source generators `srcZ i` are nilpotent of index `4 ^ i`. -/
theorem srcZ_pow_eq_zero (i : ℕ+) : srcZ k i ^ (4 ^ (i : ℕ)) = 0 := by
  rw [srcZ, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inr ⟨i, rfl⟩))

/-- The target generators `tgtX i` are nilpotent of index `4 ^ i`. -/
theorem tgtX_pow_eq_zero (i : ℕ+) : tgtX k i ^ (4 ^ (i : ℕ)) = 0 := by
  rw [tgtX, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inl ⟨i, rfl⟩))

/-- The target generators satisfy the recurrence `y i = x (i + 1) * y (i + 1) ^ 2`. -/
theorem tgtY_eq (i : ℕ+) : tgtY k i = tgtX k (i + 1) * tgtY k (i + 1) ^ 2 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (tgtIdeal k) (X (TgtVar.y i)) -
    Ideal.Quotient.mk (tgtIdeal k) (X (TgtVar.x (i + 1))) *
      Ideal.Quotient.mk (tgtIdeal k) (X (TgtVar.y (i + 1))) ^ 2 = 0
  rw [← map_pow, ← map_mul, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inr ⟨i, rfl⟩))

/-- Each `y i` is nilpotent of index `4 ^ (i + 1)`. -/
theorem tgtY_pow_eq_zero (i : ℕ+) : tgtY k i ^ (4 ^ ((i : ℕ) + 1)) = 0 := by
  rw [tgtY_eq k i, mul_pow]
  have hx : tgtX k (i + 1) ^ (4 ^ ((i : ℕ) + 1)) = 0 :=
    tgtX_pow_eq_zero k (i + 1)
  rw [hx, zero_mul]

private theorem srcToTgt_component_one_eq_zero (p : MvPolynomial SrcVar k) :
    weightedHomogeneousComponent tgtDeg 1 (srcToTgt k p) = 0 := by
  classical
  have hhom {q : MvPolynomial TgtVar k} {n : ℤ}
      (hq : q.IsWeightedHomogeneous tgtDeg n) (hn : n ≤ 0) :
      ∀ m ∈ q.support, Finsupp.weight tgtDeg m ≤ 0 := by
    intro m hm
    rw [hq (mem_support_iff.mp hm)]
    exact hn
  have hmul (p q : MvPolynomial TgtVar k)
      (hp : ∀ m ∈ p.support, Finsupp.weight tgtDeg m ≤ 0)
      (hq : ∀ m ∈ q.support, Finsupp.weight tgtDeg m ≤ 0) :
      ∀ m ∈ (p * q).support, Finsupp.weight tgtDeg m ≤ 0 := by
    intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
    simpa only [map_add] using add_nonpos (hp a ha) (hq b hb)
  have hp : ∀ m ∈ (srcToTgt k p).support, Finsupp.weight tgtDeg m ≤ 0 := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      simpa [srcToTgt] using hhom (isWeightedHomogeneous_C tgtDeg c) le_rfl
    | add p q hp hq =>
      rw [map_add]
      intro m hm
      rcases Finset.mem_union.mp (support_add hm) with hm | hm
      · exact hp m hm
      · exact hq m hm
    | mul_X p v hp =>
      rw [map_mul]
      apply hmul _ _ hp
      cases v with
      | x i =>
        simpa [srcToTgt] using
          hhom (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.x i)) (by simp [tgtDeg])
      | z i =>
        have hz : IsWeightedHomogeneous tgtDeg
            (X (TgtVar.x i) * X (TgtVar.y i) : MvPolynomial TgtVar k) 0 := by
          simpa [tgtDeg] using
            (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.x i)).mul
              (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.y i))
        simpa [srcToTgt] using hhom hz le_rfl
  apply weightedHomogeneousComponent_eq_zero'
  intro m hm hdeg
  have hle := hp m hm
  rw [hdeg] at hle
  exact (by decide : ¬ (1 : ℤ) ≤ 0) hle

end

section

variable [Field k]

private theorem quotient_local_zeroDim_of_nilpotent_vars {σ : Type*}
    (I : Ideal (MvPolynomial σ k))
    (hI : I ≤ RingHom.ker constantCoeff)
    (hX : ∀ i, IsNilpotent (Ideal.Quotient.mk I (X i))) :
    IsLocalRing (MvPolynomial σ k ⧸ I) ∧ Ring.KrullDimLE 0 (MvPolynomial σ k ⧸ I) := by
  let A := MvPolynomial σ k ⧸ I
  let f : A →+* k := Ideal.Quotient.lift I constantCoeff fun p hp ↦ hI hp
  have hf : Function.Surjective f := by
    intro c
    refine ⟨Ideal.Quotient.mk I (C c), ?_⟩
    change constantCoeff (C c : MvPolynomial σ k) = c
    exact constantCoeff_C σ c
  have hker : RingHom.ker f = nilradical A := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hc : constantCoeff p = 0 := by
        exact RingHom.mem_ker.mp ha
      let g := (Ideal.Quotient.mk (nilradical A)).comp (Ideal.Quotient.mk I)
      have hg : g = (g.comp C).comp constantCoeff := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp
        · intro i
          simp only [RingHom.comp_apply, constantCoeff_X, map_zero]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hX i)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change g p = 0
      rw [RingHom.congr_fun hg p]
      simp [hc]
    · intro a ha
      exact RingHom.mem_ker.mpr ((show IsNilpotent a from ha).map f).eq_zero
  haveI : (nilradical A).IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  exact ⟨IsLocalRing.of_isMaximal_nilradical A, Ring.KrullDimLE.of_isMaximal_nilradical A⟩

private theorem src_local_zeroDim : IsLocalRing (Src k) ∧ Ring.KrullDimLE 0 (Src k) := by
  apply quotient_local_zeroDim_of_nilpotent_vars k (srcIdeal k)
  · apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simp [RingHom.mem_ker, srcXPow]
    · simp [RingHom.mem_ker, srcZPow]
  · intro v
    cases v with
    | x i => exact ⟨_, srcX_pow_eq_zero k i⟩
    | z i => exact ⟨_, srcZ_pow_eq_zero k i⟩

private theorem tgt_local_zeroDim : IsLocalRing (Tgt k) ∧ Ring.KrullDimLE 0 (Tgt k) := by
  apply quotient_local_zeroDim_of_nilpotent_vars k (tgtIdeal k)
  · apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simp [RingHom.mem_ker, tgtXPow]
    · simp [RingHom.mem_ker, tgtYRecurrence]
  · intro v
    cases v with
    | x i => exact ⟨_, tgtX_pow_eq_zero k i⟩
    | y i => exact ⟨_, tgtY_pow_eq_zero k i⟩

/-- The source presentation is a local ring. -/
instance instIsLocalRingSrc : IsLocalRing (Src k) := (src_local_zeroDim k).1

/-- The target presentation is a local ring. -/
instance instIsLocalRingTgt : IsLocalRing (Tgt k) := (tgt_local_zeroDim k).1

/-- The source presentation has Krull dimension at most `0`. -/
instance instKrullDimLESrc : Ring.KrullDimLE 0 (Src k) := (src_local_zeroDim k).2

/-- The target presentation has Krull dimension at most `0`. -/
instance instKrullDimLETgt : Ring.KrullDimLE 0 (Tgt k) := (tgt_local_zeroDim k).2

/-- The comparison map is an epimorphism of commutative rings. -/
instance instIsEpi : Algebra.IsEpi (Src k) (Tgt k) := by
  let l : Tgt k →+* Tgt k ⊗[Src k] Tgt k := Algebra.TensorProduct.includeLeftRingHom
  let r : Tgt k →+* Tgt k ⊗[Src k] Tgt k := Algebra.TensorProduct.includeRight.toRingHom
  have hbase (s : Src k) : l (hom k s) = r (hom k s) :=
    RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap s
  have hx (i : ℕ+) : l (tgtX k i) = r (tgtX k i) := by
    simpa only [hom_srcX] using hbase (srcX k i)
  have hxy (i : ℕ+) : l (tgtX k i) * l (tgtY k i) =
      r (tgtX k i) * r (tgtY k i) := by
    simpa only [hom_srcZ, map_mul] using hbase (srcZ k i)
  have hy (i : ℕ+) : l (tgtY k i) = r (tgtY k i) := by
    rw [tgtY_eq k i, map_mul, map_mul, map_pow, map_pow]
    calc
      l (tgtX k (i + 1)) * l (tgtY k (i + 1)) ^ 2 =
          (l (tgtX k (i + 1)) * l (tgtY k (i + 1))) * l (tgtY k (i + 1)) := by ring
      _ = (r (tgtX k (i + 1)) * r (tgtY k (i + 1))) * l (tgtY k (i + 1)) := by
        rw [hxy]
      _ = (l (tgtX k (i + 1)) * l (tgtY k (i + 1))) * r (tgtY k (i + 1)) := by
        rw [← hx]
        ring
      _ = (r (tgtX k (i + 1)) * r (tgtY k (i + 1))) * r (tgtY k (i + 1)) := by
        rw [hxy]
      _ = r (tgtX k (i + 1)) * r (tgtY k (i + 1)) ^ 2 := by ring
  have hpoly : l.comp (Ideal.Quotient.mk (tgtIdeal k)) =
      r.comp (Ideal.Quotient.mk (tgtIdeal k)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa [hom, srcToTgt] using
        hbase (Ideal.Quotient.mk (srcIdeal k) (C c))
    · intro v
      cases v with
      | x i => exact hx i
      | y i => exact hy i
  refine (Algebra.isEpi_iff_forall_one_tmul_eq (Src k) (Tgt k)).mpr fun a ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (RingHom.congr_fun hpoly p).symm

/-- The generator `y 1` is nonzero in the target. -/
theorem tgtY_one_ne_zero : tgtY k 1 ≠ 0 := by
  -- In k[t^ℚ≥0]/(t), send x_i to t^(4^(-i)) and y_i to t^(4^(-i)/2).
  let M := AddMonoidAlgebra k ℚ≥0
  let J : Ideal M := Ideal.span (AddMonoidAlgebra.of' k ℚ≥0 '' {(1 : ℚ≥0)})
  let q : M →+* M ⧸ J := Ideal.Quotient.mk J
  let xp : ℕ+ → ℚ≥0 := fun i ↦ ((4 : ℚ≥0) ^ (i : ℕ))⁻¹
  let yp : ℕ+ → ℚ≥0 := fun i ↦ (1 / 2 : ℚ≥0) * xp i
  have hxexp (i : ℕ+) : (4 ^ (i : ℕ)) • xp i = 1 := by
    simp [xp, nsmul_eq_mul, Nat.cast_pow]
  have hsucc (i : ℕ+) : xp (i + 1) = xp i * (4 : ℚ≥0)⁻¹ := by
    simp [xp, pow_succ, mul_inv_rev, mul_comm]
  have hyexp (i : ℕ+) : yp i = xp (i + 1) + 2 • yp (i + 1) := by
    dsimp [yp]
    rw [hsucc]
    norm_num [nsmul_eq_mul]
    ring
  have hx (i : ℕ+) : (AddMonoidAlgebra.single (xp i) (1 : k)) ^ (4 ^ (i : ℕ)) =
      AddMonoidAlgebra.single 1 (1 : k) := by
    rw [AddMonoidAlgebra.single_pow, hxexp, one_pow]
  have hy (i : ℕ+) : AddMonoidAlgebra.single (yp i) (1 : k) =
      AddMonoidAlgebra.single (xp (i + 1)) (1 : k) *
        AddMonoidAlgebra.single (yp (i + 1)) (1 : k) ^ 2 := by
    simp only [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
      one_pow, one_mul]
    rw [hyexp]
  let ev : MvPolynomial TgtVar k →ₐ[k] M ⧸ J := aeval fun v ↦
    match v with
    | .x i => q (AddMonoidAlgebra.single (xp i) 1)
    | .y i => q (AddMonoidAlgebra.single (yp i) 1)
  have hrel : tgtIdeal k ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change ev (tgtXPow k i) = 0
      change ev (X (TgtVar.x i) ^ (4 ^ (i : ℕ))) = 0
      simp only [map_pow, ev, aeval_X]
      rw [← map_pow, hx]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨1, by simp, rfl⟩
    · change ev (tgtYRecurrence k i) = 0
      simp only [tgtYRecurrence, map_sub, map_mul, map_pow, ev, aeval_X]
      rw [← map_pow, ← map_mul, ← hy, sub_self]
  let f : Tgt k →+* M ⧸ J := Ideal.Quotient.lift (tgtIdeal k) ev.toRingHom
    fun p hp ↦ hrel hp
  intro h
  have hz : q (AddMonoidAlgebra.single (yp 1) (1 : k)) = 0 := by
    simpa [f, tgtY, ev] using congrArg f h
  have hm : AddMonoidAlgebra.single (yp 1) (1 : k) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hs : yp 1 ∈ (AddMonoidAlgebra.single (yp 1) (1 : k)).coeff.support := by
    simp
  obtain ⟨m, hm, d, hd⟩ := AddMonoidAlgebra.mem_ideal_span_of'_image.mp hm (yp 1) hs
  have hm₁ : m = 1 := Set.mem_singleton_iff.mp hm
  have hge : (1 : ℚ≥0) ≤ yp 1 := by
    rw [hd, hm₁]
    exact le_add_of_nonneg_left (show 0 ≤ d from zero_le)
  norm_num [yp, xp] at hge
  have hge' : (1 : ℚ) ≤ 1 / 8 := by exact_mod_cast hge
  norm_num at hge'

/-- The comparison map is not surjective. -/
theorem not_surjective : ¬ Function.Surjective (hom k) := by
  letI := weightedGradedAlgebra k tgtDeg
  have hhom : (tgtIdeal k).IsHomogeneous (weightedHomogeneousSubmodule k tgtDeg) := by
    apply Ideal.homogeneous_span
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨_, (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.x i)).pow _⟩
    · refine ⟨1, ?_⟩
      have hprod : (X (TgtVar.x (i + 1)) * X (TgtVar.y (i + 1)) ^ 2 :
          MvPolynomial TgtVar k).IsWeightedHomogeneous tgtDeg 1 := by
        simpa [tgtDeg] using
          (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.x (i + 1))).mul
            ((isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.y (i + 1))).pow 2)
      exact (weightedHomogeneousSubmodule k tgtDeg 1).sub_mem
        (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.y i)) hprod
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (tgtY k 1)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hp : srcToTgt k p - X (TgtVar.y 1) ∈ tgtIdeal k := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa [hom, tgtY] using ha
  have hp₁ := weightedHomogeneousComponent_mem_of_mem k tgtDeg hhom hp 1
  have hy₁ : weightedHomogeneousComponent tgtDeg 1 (X (TgtVar.y 1) : MvPolynomial TgtVar k) =
      X (TgtVar.y 1) :=
    (isWeightedHomogeneous_X (R := k) tgtDeg (TgtVar.y 1)).weightedHomogeneousComponent_same
  rw [map_sub, srcToTgt_component_one_eq_zero, hy₁, zero_sub] at hp₁
  exact tgtY_one_ne_zero k (Ideal.Quotient.eq_zero_iff_mem.mpr (neg_mem_iff.mp hp₁))

end

end ZeroDimEpi

namespace RingHom

/-- There exists a nonsurjective epimorphism between local commutative rings of Krull
dimension zero. -/
@[stacks 06RI]
theorem exists_isLocalRing_krullDimLE_zero_isEpi_not_surjective :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S)
      (_ : IsLocalRing R) (_ : IsLocalRing S) (_ : Ring.KrullDimLE 0 R)
      (_ : Ring.KrullDimLE 0 S),
      Algebra.IsEpi R S ∧ ¬ Function.Surjective (algebraMap R S) := by
  refine ⟨ZeroDimEpi.Src (ULift.{u} ℚ), ZeroDimEpi.Tgt (ULift.{u} ℚ),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  exact ⟨inferInstance, ZeroDimEpi.not_surjective (ULift.{u} ℚ)⟩

end RingHom
