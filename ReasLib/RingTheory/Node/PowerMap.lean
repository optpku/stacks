/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Node.CoordinateRing
public import ReasLib.RingTheory.Localization.TotalQuotient.Product
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open MvPolynomial
open scoped TensorProduct

universe u

noncomputable section

namespace NodeCoordinateRing

variable (k : Type u) [Field k]

/-- The polynomial algebra homomorphism sending the nodal coordinates to their prescribed powers. -/
def powerPolynomialMap (n m : ℕ+) :
    MvPolynomial (Fin 2) k →ₐ[k] Ring k :=
  MvPolynomial.eval₂AlgHom k fun i ↦
    coordinate k i ^ if i = 0 then (n : ℕ) else (m : ℕ)

/-- The polynomial power map evaluated on a coordinate variable. -/
theorem powerPolynomialMap_X (n m : ℕ+) (i : Fin 2) :
    powerPolynomialMap k n m (X i) =
      coordinate k i ^ if i = 0 then (n : ℕ) else (m : ℕ) := by
  simp [powerPolynomialMap]

/-- The nodal equation ideal is contained in the kernel of the polynomial power map. -/
theorem ideal_le_powerPolynomialMap_ker (n m : ℕ+) :
    ideal k ≤ RingHom.ker (powerPolynomialMap k n m).toRingHom := by
  have hxy : coordinate k 0 * coordinate k 1 = 0 := by
    change Ideal.Quotient.mk (ideal k) (X 0) * Ideal.Quotient.mk (ideal k) (X 1) = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  apply Ideal.span_le.mpr
  rintro p rfl
  change powerPolynomialMap k n m (X 0 * X 1) = 0
  rw [map_mul, powerPolynomialMap_X, powerPolynomialMap_X]
  change coordinate k 0 ^ (n : ℕ) * coordinate k 1 ^ (m : ℕ) = 0
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (PNat.ne_zero n)
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (PNat.ne_zero m)
  rw [hn', hm', pow_succ, pow_succ]
  calc
    coordinate k 0 ^ n' * coordinate k 0 * (coordinate k 1 ^ m' * coordinate k 1) =
        (coordinate k 0 ^ n' * coordinate k 1 ^ m') * (coordinate k 0 * coordinate k 1) := by
      ring
    _ = 0 := by rw [hxy, mul_zero]

/-- The ring homomorphism induced by the polynomial power map on the nodal quotient. -/
def powerMap (n m : ℕ+) : Ring k →ₐ[k] Ring k :=
  Ideal.Quotient.liftₐ (ideal k) (powerPolynomialMap k n m)
    (ideal_le_powerPolynomialMap_ker k n m)

/-- The nodal power map sends the first coordinate to its `n`-th power. -/
theorem powerMap_apply_zero (n m : ℕ+) :
    powerMap k n m (coordinate k 0) = coordinate k 0 ^ (n : ℕ) := by
  simp [powerMap, coordinate, powerPolynomialMap_X]

/-- The nodal power map sends the second coordinate to its `m`-th power. -/
theorem powerMap_apply_one (n m : ℕ+) :
    powerMap k n m (coordinate k 1) = coordinate k 1 ^ (m : ℕ) := by
  simp [powerMap, coordinate, powerPolynomialMap_X]

/-- The image of the nodal coordinate sum under the power map. -/
theorem powerMap_apply_branchSum (n m : ℕ+) :
    powerMap k n m (coordinate k 0 + coordinate k 1) =
      coordinate k 0 ^ (n : ℕ) + coordinate k 1 ^ (m : ℕ) := by
  rw [map_add, powerMap_apply_zero, powerMap_apply_one]

/-- The explicit target-ring algebra structure induced by the nodal power map. -/
@[reducible]
noncomputable def powerAlgebra (n m : ℕ+) : Algebra (Ring k) (Ring k) :=
  (powerMap k n m).toRingHom.toAlgebra

/-- The structural algebra map of `powerAlgebra` is the nodal power map. -/
theorem powerAlgebra_algebraMap (n m : ℕ+) :
    @algebraMap (Ring k) (Ring k) _ _ (powerAlgebra k n m) =
      (powerMap k n m).toRingHom := rfl

private theorem powerAlgebra_moduleFinite (n m : ℕ+) :
    @Module.Finite (Ring k) (Ring k) _ _ (powerAlgebra k n m).toModule := by
  letI : Algebra (Ring k) (Ring k) := powerAlgebra k n m
  letI : Module (Ring k) (Ring k) := (powerAlgebra k n m).toModule
  let S := Algebra.adjoin (Ring k) (Set.range (coordinate k))
  have hx : IsIntegral (Ring k) (coordinate k 0) := by
    apply IsIntegral.of_pow n.pos
    rw [← powerMap_apply_zero k n m]
    exact isIntegral_algebraMap
  have hy : IsIntegral (Ring k) (coordinate k 1) := by
    apply IsIntegral.of_pow m.pos
    rw [← powerMap_apply_one k n m]
    exact isIntegral_algebraMap
  haveI : Module.Finite (Ring k) S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
      rintro b ⟨i, rfl⟩
      fin_cases i
      · exact hx
      · exact hy)
  have hS : S = ⊤ := by
    apply top_unique
    intro b hb
    clear hb
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    induction p using MvPolynomial.induction_on with
    | C a =>
      change algebraMap k (Ring k) a ∈ S
      rw [← (powerMap k n m).commutes a]
      exact S.algebraMap_mem (algebraMap k (Ring k) a)
    | add p q hp hq =>
      simpa only [map_add] using S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact Module.Finite.of_surjective S.val.toLinearMap (by
    intro b
    exact ⟨⟨b, hS.symm ▸ trivial⟩, rfl⟩)

private theorem coordinateRing_isReduced : IsReduced (Ring k) := by
  have hx : Prime (X (0 : Fin 2) : MvPolynomial (Fin 2) k) := MvPolynomial.X_prime
  have hy : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) k) := MvPolynomial.X_prime
  apply (Ideal.isRadical_iff_quotient_reduced (ideal k)).mp
  apply isRadical_iff_span_singleton.mp
  apply isRadical_iff_squarefree_or_zero.mpr
  left
  exact squarefree_mul_iff.mpr
    ⟨hx.irreducible.isRelPrime_iff_not_dvd.mpr (by simp), hx.squarefree, hy.squarefree⟩

private theorem fractionRing_isSemisimple : IsSemisimpleRing (FractionRing (Ring k)) := by
  letI : IsReduced (Ring k) := coordinateRing_isReduced k
  have hfinite := minimalPrimes.finite_of_isNoetherianRing (Ring k)
  letI : Finite (minimalPrimes (Ring k)) := hfinite.to_subtype
  letI (q : minimalPrimes (Ring k)) : q.val.IsPrime := q.property.isPrime
  exact (Localization.totalQuotientEquivFractionRingPi (Ring k) hfinite).symm.isSemisimpleRing

/-- The generic fibre of the nodal power map as a tensor product with the source fraction ring. -/
noncomputable def GenericFiber (n m : ℕ+) :=
  @TensorProduct (Ring k) _ (Ring k) (FractionRing (Ring k)) _ _
    (powerAlgebra k n m).toModule _

/-- The commutative-ring structure on the generic fibre tensor product. -/
noncomputable instance genericFiberCommRing (n m : ℕ+) :
    CommRing (GenericFiber k n m) :=
  @Algebra.TensorProduct.instCommRing
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The canonical map from the target nodal ring into the generic fibre. -/
def genericFiberTargetMap (n m : ℕ+) : Ring k →+* GenericFiber k n m :=
  @Algebra.TensorProduct.includeLeftRingHom
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The canonical map from the source total fraction ring into the generic fibre. -/
def genericFiberFractionMap (n m : ℕ+) :
    FractionRing (Ring k) →+* GenericFiber k n m :=
  (@Algebra.TensorProduct.includeRight
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _).toRingHom

/-- The target nodal ring algebra structure on the generic fibre. -/
noncomputable instance genericFiberTargetAlgebra (n m : ℕ+) :
    Algebra (Ring k) (GenericFiber k n m) :=
  (genericFiberTargetMap k n m).toAlgebra

/-- The fraction-ring algebra structure on the generic fibre. -/
noncomputable instance genericFiberFractionAlgebra (n m : ℕ+) :
    Algebra (FractionRing (Ring k)) (GenericFiber k n m) :=
  @Algebra.TensorProduct.rightAlgebra
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The generic fibre is finite over the source fraction ring. -/
noncomputable instance genericFiber_moduleFinite (n m : ℕ+) :
    Module.Finite (FractionRing (Ring k)) (GenericFiber k n m) := by
  classical
  obtain ⟨s, hs⟩ := (powerAlgebra_moduleFinite k n m).fg_top
  let P : Submodule (FractionRing (Ring k)) (GenericFiber k n m) :=
    Submodule.span _ (s.image (genericFiberTargetMap k n m) : Set (GenericFiber k n m))
  have hcompat (a : Ring k) :
      genericFiberTargetMap k n m (powerMap k n m a) =
        algebraMap (FractionRing (Ring k)) (GenericFiber k n m)
          (algebraMap (Ring k) (FractionRing (Ring k)) a) :=
    ((@Algebra.TensorProduct.includeRight
      (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _).commutes a).symm
  have hmul (b : Ring k) (q : FractionRing (Ring k)) :
      q • genericFiberTargetMap k n m b =
        @TensorProduct.tmul (Ring k) _ (Ring k) (FractionRing (Ring k)) _ _
          (powerAlgebra k n m).toModule _ b q := by
    rw [Algebra.smul_def]
    change genericFiberFractionMap k n m q * genericFiberTargetMap k n m b = _
    change
      (@TensorProduct.tmul (Ring k) _ (Ring k) (FractionRing (Ring k)) _ _
          (powerAlgebra k n m).toModule _ 1 q) *
        (@TensorProduct.tmul (Ring k) _ (Ring k) (FractionRing (Ring k)) _ _
          (powerAlgebra k n m).toModule _ b 1) = _
    simpa only [one_mul, mul_one] using
      (@Algebra.TensorProduct.tmul_mul_tmul (Ring k) (Ring k) (FractionRing (Ring k))
        _ _ (powerAlgebra k n m).toModule
        (@Algebra.to_smulCommClass (Ring k) (Ring k) _ _ (powerAlgebra k n m))
        (@IsScalarTower.right (Ring k) (Ring k) _ _ (powerAlgebra k n m))
        _ _ _ _ 1 b q 1)
  let f := algebraMap (Ring k) (FractionRing (Ring k))
  have hb (b : Ring k) : genericFiberTargetMap k n m b ∈ P := by
    letI : Module (Ring k) (Ring k) := (powerAlgebra k n m).toModule
    have h : b ∈ (⊤ : @Submodule (Ring k) (Ring k) _ _ (powerAlgebra k n m).toModule) :=
      Submodule.mem_top
    rw [← hs] at h
    induction h using Submodule.span_induction with
    | mem b hb =>
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    | zero =>
      simpa only [map_zero] using P.zero_mem
    | add b c hb hc ihb ihc =>
      simpa only [map_add] using P.add_mem ihb ihc
    | smul a b hb ih =>
      change genericFiberTargetMap k n m (powerMap k n m a * b) ∈ P
      rw [map_mul, hcompat]
      simpa only [Algebra.smul_def] using
        P.smul_mem (f a) ih
  refine ⟨⟨s.image (genericFiberTargetMap k n m), ?_⟩⟩
  change P = ⊤
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact P.zero_mem
  | add z w hz hw => exact P.add_mem hz hw
  | tmul b q =>
    simpa only [hmul] using P.smul_mem q (hb b)

/-- The generic fibre is projective over the source fraction ring. -/
noncomputable instance genericFiber_moduleProjective (n m : ℕ+) :
    Module.Projective (FractionRing (Ring k)) (GenericFiber k n m) := by
  exact @Module.projective_of_isSemisimpleRing (FractionRing (Ring k)) _
    (fractionRing_isSemisimple k) (GenericFiber k n m) _
    (genericFiberFractionAlgebra k n m).toModule

/-- The nodal power map is finite as a ring homomorphism. -/
theorem powerMap_finite (n m : ℕ+) :
    RingHom.Finite (powerMap k n m).toRingHom := powerAlgebra_moduleFinite k n m

/-- The localization map induced by the nodal power map. -/
def localizedPowerMap (n m : ℕ+) :
    Localization.Away (coordinate k 0 + coordinate k 1) →+*
      Localization.Away (powerMap k n m (coordinate k 0 + coordinate k 1)) :=
  Localization.awayMap (powerMap k n m).toRingHom (coordinate k 0 + coordinate k 1)

/-- The localized power map agrees with the power map on coefficient classes. -/
theorem localizedPowerMap_apply_algebraMap (n m : ℕ+) (a : Ring k) :
    localizedPowerMap k n m
        (algebraMap (Ring k) (Localization.Away (coordinate k 0 + coordinate k 1)) a) =
      algebraMap (Ring k)
        (Localization.Away (powerMap k n m (coordinate k 0 + coordinate k 1)))
        (powerMap k n m a) := by
  simpa [localizedPowerMap, Localization.awayMap, IsLocalization.Away.map] using
    (IsLocalization.map_eq
      (g := (powerMap k n m).toRingHom)
      (S := Localization.Away (coordinate k 0 + coordinate k 1))
      (Q := Localization.Away (powerMap k n m (coordinate k 0 + coordinate k 1)))
      (M := Submonoid.powers (coordinate k 0 + coordinate k 1))
      (T := Submonoid.powers (powerMap k n m (coordinate k 0 + coordinate k 1)))
      _ a)

/-- The localization of the nodal power map is finite when both exponents are units. -/
theorem localizedPowerMap_finite (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    RingHom.Finite (localizedPowerMap k n m) := by
  exact RingHom.finite_localizationPreserves.away
    (powerMap k n m).toRingHom (coordinate k 0 + coordinate k 1) _ _ (powerMap_finite k n m)

/-- The localization of the nodal power map is étale when both exponents are units. -/
theorem localizedPowerMap_etale (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    RingHom.Etale (localizedPowerMap k n m) := sorry

end NodeCoordinateRing
