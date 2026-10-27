/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.Projective
public import ReasLib.RingTheory.Node.PowerMap
public import ReasLib.RingTheory.RingHom.Unramified
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

universe u

noncomputable section

namespace NodeCoordinateRing

variable (k : Type u) [Field k]

/-- The finite-projective trace of the generic fibre over the source fraction ring. -/
noncomputable def genericTrace (n m : ℕ+) :
    GenericFiber k n m →ₗ[FractionRing (Ring k)] FractionRing (Ring k) :=
  Algebra.FiniteProjective.trace (FractionRing (Ring k)) (GenericFiber k n m)

/-- The zero element satisfies the trace-integrality carrier condition. -/
theorem complementary_zero (n m : ℕ+) :
    ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * 0) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range := by
  intro b
  simp

/-- The trace-integrality carrier is closed under addition. -/
theorem complementary_add (n m : ℕ+) (x y : GenericFiber k n m)
    (hx : ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * x) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range)
    (hy : ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * y) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range) :
    ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * (x + y)) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range := by
  intro b
  rw [mul_add, map_add]
  exact (algebraMap (Ring k) (FractionRing (Ring k))).range.add_mem (hx b) (hy b)

/-- The trace-integrality carrier is closed under the target-ring scalar action. -/
theorem complementary_smul (n m : ℕ+) (a : Ring k) (x : GenericFiber k n m)
    (hx : ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * x) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range) :
    ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * (a • x)) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range := by
  intro b
  change genericTrace k n m
    (genericFiberTargetMap k n m b * (genericFiberTargetMap k n m a * x)) ∈ _
  rw [← mul_assoc, ← map_mul]
  exact hx (b * a)

/-- The trace-integral complementary submodule of the nodal generic fibre. -/
noncomputable def complementary (n m : ℕ+) :
    Submodule (Ring k) (GenericFiber k n m) where
  carrier := {z | ∀ b : Ring k,
    genericTrace k n m (genericFiberTargetMap k n m b * z) ∈
      (algebraMap (Ring k) (FractionRing (Ring k))).range}
  zero_mem' := complementary_zero k n m
  add_mem' := by
    intro x y hx hy
    exact complementary_add k n m x y hx hy
  smul_mem' := by
    intro a x hx
    exact complementary_smul k n m a x hx

/-- Membership in `complementary` is the trace-integrality condition for every target element. -/
theorem mem_complementary_iff (n m : ℕ+) (z : GenericFiber k n m) :
    z ∈ complementary k n m ↔ ∀ b : Ring k,
      genericTrace k n m (genericFiberTargetMap k n m b * z) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range := Iff.rfl

/-- The Dedekind different of the nodal generic fibre over the target nodal ring. -/
noncomputable def dedekindDifferent (n m : ℕ+) :
    Submodule (Ring k) (GenericFiber k n m) :=
  (1 : Submodule (Ring k) (GenericFiber k n m)) / complementary k n m

/-- Membership in the Dedekind different is the multiplication condition against the
complementary submodule. -/
theorem mem_dedekindDifferent_iff (n m : ℕ+) (z : GenericFiber k n m) :
    z ∈ dedekindDifferent k n m ↔
      ∀ y ∈ complementary k n m,
        z * y ∈ (1 : Submodule (Ring k) (GenericFiber k n m)) := by
  rfl

/-- The target-ring different ideal is the inverse image of the Dedekind different. -/
noncomputable def differentIdeal (n m : ℕ+) : Ideal (Ring k) :=
  Submodule.comap (Algebra.linearMap (Ring k) (GenericFiber k n m))
    (dedekindDifferent k n m)

/-- Membership in the target-ring different ideal is membership after the generic-fibre map. -/
theorem mem_differentIdeal_iff (n m : ℕ+) (b : Ring k) :
    b ∈ differentIdeal k n m ↔
      genericFiberTargetMap k n m b ∈ dedekindDifferent k n m := Iff.rfl

/-- The trace-extension criterion in arbitrary characteristic is equality of exponent images. -/
theorem one_mem_complementary_cast_iff (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    (1 : GenericFiber k n m) ∈ complementary k n m ↔
      ((n : ℕ) : k) = ((m : ℕ) : k) := sorry

/-- The trace of the generic-fibre unit after clearing the branch-sum denominator. -/
theorem trace_one (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    genericTrace k n m (1 : GenericFiber k n m) *
        algebraMap (Ring k) (FractionRing (Ring k))
          (coordinate k 0 + coordinate k 1) =
      algebraMap (Ring k) (FractionRing (Ring k))
        (((n : ℕ) : Ring k) * coordinate k 0 +
          ((m : ℕ) : Ring k) * coordinate k 1) := sorry

/-- The generic-fibre trace vanishes on powers of the first coordinate below `n`. -/
theorem trace_left_pow (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (i : ℕ) (hi : 1 ≤ i) (hin : i < (n : ℕ)) :
    genericTrace k n m
      (genericFiberTargetMap k n m (coordinate k 0 ^ i)) = 0 := sorry

/-- The generic-fibre trace vanishes on powers of the second coordinate below `m`. -/
theorem trace_right_pow (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (j : ℕ) (hj : 1 ≤ j) (hjm : j < (m : ℕ)) :
    genericTrace k n m
      (genericFiberTargetMap k n m (coordinate k 1 ^ j)) = 0 := sorry

/-- Under characteristic zero, trace-extension exists exactly when the natural exponents agree. -/
theorem one_mem_complementary_iff (n m : ℕ+)
    [CharZero k]
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    (1 : GenericFiber k n m) ∈ complementary k n m ↔ n = m := by
  rw [one_mem_complementary_cast_iff k n m hn hm, Nat.cast_inj, PNat.coe_inj]

/-- Equal exponent images make the complementary submodule the canonical unit submodule. -/
theorem complementary_eq_one (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (h_nm : ((n : ℕ) : k) = ((m : ℕ) : k)) :
    complementary k n m = (1 : Submodule (Ring k) (GenericFiber k n m)) := sorry

/-- Equal exponent images make the Dedekind different the canonical unit submodule. -/
theorem dedekindDifferent_eq_one (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (h_nm : ((n : ℕ) : k) = ((m : ℕ) : k)) :
    dedekindDifferent k n m = (1 : Submodule (Ring k) (GenericFiber k n m)) := by
  change (1 : Submodule (Ring k) (GenericFiber k n m)) / complementary k n m = 1
  rw [complementary_eq_one k n m hn hm h_nm]
  apply le_antisymm
  · show (1 : Submodule (Ring k) (GenericFiber k n m)) / 1 ≤ 1
    intro z hz
    simpa only [mul_one] using
      (Submodule.mem_div_iff_forall_mul_mem.mp hz) 1
        (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  · show (1 : Submodule (Ring k) (GenericFiber k n m)) ≤ 1 / 1
    rw [Submodule.le_div_iff_mul_le]
    simp

/-- Equal exponent images make the target-ring different the top ideal. -/
theorem differentIdeal_eq_top (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (h_nm : ((n : ℕ) : k) = ((m : ℕ) : k)) :
    differentIdeal k n m = ⊤ := by
  apply top_unique
  intro b hb
  rw [mem_differentIdeal_iff, dedekindDifferent_eq_one k n m hn hm h_nm]
  exact Submodule.algebraMap_mem b

/-- The finite affine dual of the target nodal ring for its explicit power algebra. -/
abbrev PowerDual (n m : ℕ+) :=
  @Module.Dual (Ring k) (Ring k) _ _ (powerAlgebra k n m).toModule

/-- A trace lift exists exactly when the two exponent images in the field agree. -/
theorem exists_traceLift_iff (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    (∃ t : PowerDual k n m, ∀ b : Ring k,
      algebraMap (Ring k) (FractionRing (Ring k)) (t b) =
        genericTrace k n m (genericFiberTargetMap k n m b)) ↔
      ((n : ℕ) : k) = ((m : ℕ) : k) := by
  rw [← one_mem_complementary_cast_iff k n m hn hm]
  constructor
  · show (∃ t : PowerDual k n m, ∀ b : Ring k,
      algebraMap (Ring k) (FractionRing (Ring k)) (t b) =
        genericTrace k n m (genericFiberTargetMap k n m b)) →
      (1 : GenericFiber k n m) ∈ complementary k n m
    rintro ⟨t, ht⟩
    apply (mem_complementary_iff k n m 1).mpr
    intro b
    simpa only [mul_one] using
      (show genericTrace k n m (genericFiberTargetMap k n m b) ∈
        (algebraMap (Ring k) (FractionRing (Ring k))).range from ⟨t b, ht b⟩)
  · show (1 : GenericFiber k n m) ∈ complementary k n m → _
    intro h
    have hmem (b : Ring k) :
        genericTrace k n m (genericFiberTargetMap k n m b) ∈
          LinearMap.range (Algebra.linearMap (Ring k) (FractionRing (Ring k))) := by
      obtain ⟨a, ha⟩ := (mem_complementary_iff k n m 1).mp h b
      exact ⟨a, by simpa only [Algebra.linearMap_apply, mul_one] using ha⟩
    have hinj := IsFractionRing.injective (Ring k) (FractionRing (Ring k))
    -- Invert the canonical injection only on its range; injectivity is proved in mathlib.
    let e := LinearEquiv.ofInjective
      (Algebra.linearMap (Ring k) (FractionRing (Ring k))) hinj
    let t₀ : Ring k → Ring k := fun b ↦
      e.symm ⟨genericTrace k n m (genericFiberTargetMap k n m b), hmem b⟩
    have ht₀ (b : Ring k) :
        algebraMap (Ring k) (FractionRing (Ring k)) (t₀ b) =
          genericTrace k n m (genericFiberTargetMap k n m b) := by
      simpa only [t₀, e, Algebra.linearMap_apply] using
        (LinearEquiv.ofInjective_symm_apply
          (Algebra.linearMap (Ring k) (FractionRing (Ring k))) (h := hinj)
          ⟨genericTrace k n m (genericFiberTargetMap k n m b), hmem b⟩)
    have hcompat (a : Ring k) :
        genericFiberTargetMap k n m (powerMap k n m a) =
          algebraMap (FractionRing (Ring k)) (GenericFiber k n m)
            (algebraMap (Ring k) (FractionRing (Ring k)) a) :=
      ((@Algebra.TensorProduct.includeRight
        (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _).commutes a).symm
    let t : PowerDual k n m :=
      @LinearMap.mk _ _ _ _ (RingHom.id (Ring k)) (Ring k) (Ring k)
        _ _ (powerAlgebra k n m).toModule _
        { toFun := t₀
          map_add' := by
            intro b c
            apply hinj
            simp only [ht₀, map_add] }
        (by
          intro a b
          apply hinj
          change algebraMap (Ring k) (FractionRing (Ring k)) (t₀ (powerMap k n m a * b)) =
            algebraMap (Ring k) (FractionRing (Ring k)) (a * t₀ b)
          rw [ht₀, map_mul (genericFiberTargetMap k n m),
            map_mul (algebraMap (Ring k) (FractionRing (Ring k))), ht₀, hcompat]
          simpa [Algebra.smul_def] using
            (genericTrace k n m).map_smul
              (algebraMap (Ring k) (FractionRing (Ring k)) a) (genericFiberTargetMap k n m b))
    exact ⟨t, ht₀⟩

/-- A trace lift generates the full finite affine dual when the exponent images are units and agree. -/
theorem traceLift_generates_dual (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k)))
    (h_nm : ((n : ℕ) : k) = ((m : ℕ) : k))
    (t : PowerDual k n m)
    (ht : ∀ b : Ring k,
      algebraMap (Ring k) (FractionRing (Ring k)) (t b) =
        genericTrace k n m (genericFiberTargetMap k n m b))
    (φ : PowerDual k n m) :
    ∃ b : Ring k, ∀ c : Ring k, φ c = t (b * c) := sorry

/-- A common exponent greater than one gives a nonflat nodal power map. -/
theorem powerMap_not_flat_of_one_lt (n : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (h_one_lt : 1 < (n : ℕ)) :
    ¬(powerMap k n n).toRingHom.Flat := sorry

/-- A common exponent greater than one gives a non-unramified nodal power map. -/
theorem powerMap_not_unramified_of_one_lt (n : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (h_one_lt : 1 < (n : ℕ)) :
    ¬(powerMap k n n).toRingHom.Unramified := sorry

/-- A common exponent greater than one gives a non-étale nodal power map. -/
theorem powerMap_not_etale_of_one_lt (n : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (h_one_lt : 1 < (n : ℕ)) :
    ¬RingHom.Etale (powerMap k n n).toRingHom := by
  intro h
  exact powerMap_not_flat_of_one_lt k n hn h_one_lt
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).1

end NodeCoordinateRing
