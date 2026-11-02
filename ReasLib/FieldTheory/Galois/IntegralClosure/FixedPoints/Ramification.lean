/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Galois.IntegralClosure.Etale
public import ReasLib.FieldTheory.Galois.IntegralClosure.FixedPoints.ResidueField
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.FixedPoints.ResidueField

@[expose] public section

/-!
# Ramification in fixed-subalgebra towers

The numerical branch data of a fixed-subalgebra tower is controlled by intersections with the
ambient inertia subgroup.  The source-facing wild/tame specializations are kept as thin corollaries
of this subgroup-level owner.
@stack 0BU6
-/

universe u v w

namespace integralClosure.FixedPoints.Ramification

open Ideal IsLocalRing
open scoped Pointwise

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- When the lower fixed subgroup contains wild inertia, the ramification index between nested
fixed subalgebras is the relative index of their intersections with inertia.  The wild-range
hypothesis is essential: without it, an inseparable residue contribution need not be represented
by the inertia subgroup index. -/
@[stacks 0BU6 "fixed-subalgebra ramification index as an inertia relative index"]
theorem ramificationIdx_eq_inertiaRelIndex_of_wild_le
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H H' : Subgroup Gal(L / K)}
    (hP : m.wildInertia Gal(L / K) ≤ H) (h : H ≤ H')
    (hfix : H' ≤ MulAction.stabilizer Gal(L / K) m) :
    -- Local instance justification (defeq pin): the ramification index uses the canonical
    -- fixed-subalgebra inclusion selected by `FixedPoints.subalgebraAlgebraOfLe h`.
    letI : Algebra
        (FixedPoints.subalgebra A (integralClosure A L) H')
        (FixedPoints.subalgebra A (integralClosure A L) H) :=
      FixedPoints.subalgebraAlgebraOfLe h
    Ideal.ramificationIdx
        (m.under (FixedPoints.subalgebra A (integralClosure A L) H))
        (FixedPoints.subalgebra A (integralClosure A L) H') =
      (H ⊓ m.inertia Gal(L / K)).relIndex
      (H' ⊓ m.inertia Gal(L / K)) := sorry

-- Proof strategy: apply the Galois branch formula for ramification in the nested fixed-field
-- tower.  The relative inertia groups are `H ⊓ inertia` and `H' ⊓ inertia`; the hypothesis
-- `wildInertia ≤ H` removes the inseparable residue contribution, so the valuation ramification
-- index is exactly their relative subgroup index.  Transport the field statement through the two
-- fixed-subalgebra integral-closure identifications.

namespace Wild

/-- If the upper fixed subgroup lies between inertia and decomposition, its ramification index
down to the wild fixed subalgebra is the tame inertia order. -/
@[stacks 0BU6 "fixed-subalgebra ramification index is tame inertia order"]
theorem ramificationIdx_eq_tameCard
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H' : Subgroup Gal(L / K)}
    (hI : m.inertia Gal(L / K) ≤ H')
    (hD : H' ≤ MulAction.stabilizer Gal(L / K) m) :
    letI : Algebra
        (FixedPoints.subalgebra A (integralClosure A L) H')
        (FixedPoints.subalgebra A (integralClosure A L) (m.wildInertia Gal(L / K))) :=
      FixedPoints.subalgebraAlgebraOfLe
        ((Ideal.wildInertia_le_inertia m).trans hI)
    Ideal.ramificationIdx
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L) (m.wildInertia Gal(L / K))))
        (FixedPoints.subalgebra A (integralClosure A L) H') =
      Nat.card (m.tameInertia Gal(L / K)) := by
  have he := ramificationIdx_eq_inertiaRelIndex_of_wild_le (K := K) m le_rfl
    ((Ideal.wildInertia_le_inertia m).trans hI) hD
  rw [inf_eq_left.mpr (Ideal.wildInertia_le_inertia m), inf_eq_right.mpr hI] at he
  exact he

-- Proof strategy: specialize `ramificationIdx_eq_inertiaRelIndex_of_wild_le` to the lower subgroup
-- `wildInertia`.  Rewrite the two intersections using `wildInertia_le_inertia` and `hI`; identify
-- the resulting relative index with the cardinality of the quotient
-- `inertia / wildInertia`, namely `Ideal.tameInertia`.

/-- The residue-field extension from an upper fixed subgroup to the wild fixed subgroup is
separable. -/
@[stacks 0BU6 "wild fixed-subalgebra residue extension is separable"]
theorem residue_isSeparable
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H' : Subgroup Gal(L / K)}
    (hP : m.wildInertia Gal(L / K) ≤ H')
    (hD : H' ≤ MulAction.stabilizer Gal(L / K) m) :
    letI : Algebra
        (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (m.wildInertia Gal(L / K)))).ResidueField :=
      FixedPoints.ResidueField.algebraOfLe hP m
    Algebra.IsSeparable
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField
      (m.under
        (FixedPoints.subalgebra A (integralClosure A L)
          (m.wildInertia Gal(L / K)))).ResidueField := sorry

-- Proof strategy: use the residue extension attached to the quotient between `H'` and wild
-- inertia.  Its inseparable kernel is controlled by wild inertia; `hP` kills that kernel, while
-- `hD` supplies the decomposition-group action.  Apply the invariant residue normality theorem
-- and the wild-inertia separability criterion from `integralClosure.Tame`.

/-- The residue-field map from a subgroup-fixed contraction to the wild-fixed contraction is
bijective when the subgroup lies between wild inertia and inertia. -/
@[stacks 0BU6 "wild fixed-subalgebra residue map is bijective"]
theorem residueMap_bijective
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H' : Subgroup Gal(L / K)}
    (hP : m.wildInertia Gal(L / K) ≤ H')
    (hI : H' ≤ m.inertia Gal(L / K)) :
    letI : Algebra
        (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (m.wildInertia Gal(L / K)))).ResidueField :=
      FixedPoints.ResidueField.algebraOfLe hP m
    Function.Bijective (algebraMap
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField
      (m.under
        (FixedPoints.subalgebra A (integralClosure A L)
          (m.wildInertia Gal(L / K)))).ResidueField) := sorry

-- Proof strategy: the subgroup interval from wild inertia to `H' ≤ inertia` is totally ramified,
-- so its residue extension has degree one.  Combine `residue_isSeparable` with the fact that the
-- quotient action is contained in inertia, then use injectivity of a field algebra map and the
-- resulting one-dimensionality to prove bijectivity of the named residue map.

/-- The tame fixed-subalgebra ramification index is prime to every prime represented in the upper
residue-field characteristic. -/
@[stacks 0BU6 "fixed-subalgebra tame ramification coprimality"]
theorem ramificationIdx_coprime_of_charP
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H' : Subgroup Gal(L / K)}
    (hP : m.wildInertia Gal(L / K) ≤ H')
    (hD : H' ≤ MulAction.stabilizer Gal(L / K) m)
    (q : ℕ) [Fact q.Prime]
    [CharP
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField q] :
    letI : Algebra
        (FixedPoints.subalgebra A (integralClosure A L) H')
        (FixedPoints.subalgebra A (integralClosure A L) (m.wildInertia Gal(L / K))) :=
      FixedPoints.subalgebraAlgebraOfLe hP
    Nat.Coprime
      (Ideal.ramificationIdx
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L) (m.wildInertia Gal(L / K))))
        (FixedPoints.subalgebra A (integralClosure A L) H')) q := by
  letI : Algebra (IsLocalRing.maximalIdeal A).ResidueField
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField :=
    integralClosure.FixedPoints.ResidueField.algebraOfBase H' m
  have hchar : ringChar (IsLocalRing.maximalIdeal A).ResidueField = q :=
    (Algebra.ringChar_eq (IsLocalRing.maximalIdeal A).ResidueField
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField).trans
        (ringChar.eq
          (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField q)
  have hcop := integralClosure.Tame.tameInertiaCard_coprime_ringChar (K := K) m
    (by rw [hchar]; exact (Fact.out : q.Prime).ne_zero)
  rw [hchar] at hcop
  rw [ramificationIdx_eq_inertiaRelIndex_of_wild_le (K := K) m le_rfl hP hD,
    inf_eq_left.mpr (Ideal.wildInertia_le_inertia m)]
  apply Nat.Coprime.of_dvd_left _ hcop
  change (m.wildInertia Gal(L / K)).relIndex (H' ⊓ m.inertia Gal(L / K)) ∣
    (m.wildInertia Gal(L / K)).relIndex (m.inertia Gal(L / K))
  exact ⟨_, (Subgroup.relIndex_mul_relIndex _ _ _
    (le_inf hP (Ideal.wildInertia_le_inertia m)) inf_le_right).symm⟩

-- The relative index divides the full tame quotient order, even when `H'` does not contain
-- inertia.  The canonical base residue map identifies the two residue characteristics.

/-- The tame fixed-subalgebra index is either unramified in characteristic zero or prime to the
upper residue characteristic. -/
@[stacks 0BU6 "fixed-subalgebra tame ramification characteristic dichotomy"]
theorem ramificationIdx_coprime_or_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {H' : Subgroup Gal(L / K)}
    (hP : m.wildInertia Gal(L / K) ≤ H')
    (hD : H' ≤ MulAction.stabilizer Gal(L / K) m) :
    letI : Algebra
        (FixedPoints.subalgebra A (integralClosure A L) H')
        (FixedPoints.subalgebra A (integralClosure A L) (m.wildInertia Gal(L / K))) :=
      FixedPoints.subalgebraAlgebraOfLe hP
    ringChar
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField = 0 ∨
      Nat.Coprime
        (Ideal.ramificationIdx
          (m.under
            (FixedPoints.subalgebra A (integralClosure A L)
              (m.wildInertia Gal(L / K))))
          (FixedPoints.subalgebra A (integralClosure A L) H'))
        (ringChar
          (m.under
            (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField) := by
  rcases CharP.char_is_prime_or_zero
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField
      (ringChar
        (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField) with
      hprime | hzero
  · letI : Fact (ringChar
        (m.under (FixedPoints.subalgebra A (integralClosure A L) H')).ResidueField).Prime :=
      ⟨hprime⟩
    exact Or.inr (ramificationIdx_coprime_of_charP (K := K) m hP hD _)
  · exact Or.inl hzero

-- Proof strategy: split on whether the upper residue-field characteristic is zero.  In the
-- nonzero case, use primality of the characteristic to install the corresponding `CharP`
-- instance and apply `ramificationIdx_coprime_of_charP`.

/-- The base-to-wild fixed-subalgebra ramification index is the tame inertia order. -/
@[stacks 0BU6 "base-to-wild fixed-subalgebra ramification index"]
theorem base_ramificationIdx_eq_tameCard
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Ideal.ramificationIdx
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (m.wildInertia Gal(L / K))))
        A = Nat.card (m.tameInertia Gal(L / K)) := by
  let D := MulAction.stabilizer Gal(L / K) m
  let P := m.wildInertia Gal(L / K)
  let BD := FixedPoints.subalgebra A (integralClosure A L) D
  let BP := FixedPoints.subalgebra A (integralClosure A L) P
  let FD := IntermediateField.fixedField D
  let d := m.under BD
  let p := m.under BP
  letI : Algebra BD FD := integralClosure.FixedPoints.toFixedFieldAlgebra D
  haveI : IsScalarTower A BD FD := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  haveI : IsIntegralClosure BD A FD :=
    integralClosure.FixedPoints.isIntegralClosure D
  haveI : IsDedekindDomain BD := IsIntegralClosure.isDedekindDomain A K FD BD
  haveI : Module.Finite A BD := IsIntegralClosure.finite A K FD BD
  letI : Algebra BD BP := FixedPoints.subalgebraAlgebraOfLe
    (Ideal.wildInertia_le_stabilizer m)
  haveI : IsScalarTower A BD BP := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  haveI : Module.IsTorsionFree BD BP := .of_smul_eq_zero fun x y h => by
    change algebraMap BD BP x * y = 0 at h
    rcases mul_eq_zero.mp h with hx | hy
    · exact Or.inl (Subtype.ext (congrArg (fun z : BP => (z : integralClosure A L)) hx))
    · exact Or.inr hy
  haveI : p.LiesOver d := FixedPoints.under_liesOver_under_of_le
    (Ideal.wildInertia_le_stabilizer m) m
  haveI : Algebra.IsEtaleAt A d :=
    integralClosure.FixedPoints.etaleAt_of_inertia_le m D (Ideal.inertia_le_stabilizer m)
  change p.ramificationIdx A = _
  rw [Ideal.ramificationIdx_tower d p, Ideal.ramificationIdx_eq_one d A, one_mul]
  exact ramificationIdx_eq_tameCard (K := K) m (Ideal.inertia_le_stabilizer m) le_rfl

-- Proof strategy: factor the base-to-wild branch through the decomposition fixed subalgebra.
-- The base-to-decomposition step is etale and has ramification index one; apply
-- `ramificationIdx_eq_tameCard` to the decomposition-to-wild step and use multiplicativity of
-- ramification indices in the resulting scalar tower.

set_option maxHeartbeats 800000 in
/-- The base-to-wild fixed-subalgebra residue extension is separable. -/
@[stacks 0BU6 "base-to-wild fixed-subalgebra residue separability"]
theorem base_residue_isSeparable
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    letI : Algebra
        (IsLocalRing.maximalIdeal A).ResidueField
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (m.wildInertia Gal(L / K)))).ResidueField :=
      integralClosure.FixedPoints.ResidueField.algebraOfBase
        (A := A) (K := K) (L := L) (m.wildInertia Gal(L / K)) m
    Algebra.IsSeparable
      (IsLocalRing.maximalIdeal A).ResidueField
      (m.under
        (FixedPoints.subalgebra A (integralClosure A L)
          (m.wildInertia Gal(L / K)))).ResidueField := by
  let D := MulAction.stabilizer Gal(L / K) m
  let P := m.wildInertia Gal(L / K)
  let BD := FixedPoints.subalgebra A (integralClosure A L) D
  let BP := FixedPoints.subalgebra A (integralClosure A L) P
  let d := m.under BD
  let p := m.under BP
  let a := IsLocalRing.maximalIdeal A
  letI : Algebra BD BP := FixedPoints.subalgebraAlgebraOfLe
    (Ideal.wildInertia_le_stabilizer m)
  letI : p.LiesOver d := FixedPoints.under_liesOver_under_of_le
    (Ideal.wildInertia_le_stabilizer m) m
  letI : d.LiesOver a :=
    integralClosure.FixedPoints.ResidueField.under_liesOver_maximalIdeal D m
  letI : p.LiesOver a :=
    integralClosure.FixedPoints.ResidueField.under_liesOver_maximalIdeal P m
  letI : Algebra a.ResidueField d.ResidueField :=
    integralClosure.FixedPoints.ResidueField.algebraOfBase D m
  letI : Algebra d.ResidueField p.ResidueField :=
    FixedPoints.ResidueField.algebraOfLe (Ideal.wildInertia_le_stabilizer m) m
  letI : Algebra a.ResidueField p.ResidueField :=
    integralClosure.FixedPoints.ResidueField.algebraOfBase P m
  letI : IsScalarTower a.ResidueField d.ResidueField p.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    symm
    rw [Ideal.ResidueField.algebraMap_algebraOfLiesOver a p,
      Ideal.ResidueField.algebraMap_algebraOfLiesOver d p,
      Ideal.ResidueField.algebraMap_algebraOfLiesOver a d]
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    rfl
  haveI : Algebra.IsSeparable a.ResidueField d.ResidueField := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ :=
      (integralClosure.FixedPoints.ResidueField.baseMap_bijective (K := K) m).surjective x
    exact isSeparable_algebraMap y
  haveI : Algebra.IsSeparable d.ResidueField p.ResidueField :=
    residue_isSeparable (K := K) m (Ideal.wildInertia_le_stabilizer m) le_rfl
  exact Algebra.IsSeparable.trans a.ResidueField d.ResidueField p.ResidueField

-- Proof strategy: factor through the decomposition-fixed contraction.  The first residue map is
-- bijective by `integralClosure.FixedPoints.ResidueField.baseMap_bijective`, while the second is
-- separable by `residue_isSeparable` with `H'` equal to the decomposition group; transport
-- separability across the resulting residue-field scalar tower.

/-- The base-to-wild fixed-subalgebra ramification index is prime to the base residue
characteristic. -/
@[stacks 0BU6 "base-to-wild fixed-subalgebra tame coprimality"]
theorem base_ramificationIdx_coprime_of_charP
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.maximalIdeal A).ResidueField q] :
    Nat.Coprime
      (Ideal.ramificationIdx
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (m.wildInertia Gal(L / K)))) A) q := by
  rw [base_ramificationIdx_eq_tameCard (K := K) m]
  have hchar := ringChar.eq (IsLocalRing.maximalIdeal A).ResidueField q
  simpa only [hchar] using
    integralClosure.Tame.tameInertiaCard_coprime_ringChar (K := K) m
      (by rw [hchar]; exact (Fact.out : q.Prime).ne_zero)

-- Proof strategy: rewrite the base ramification index with
-- `base_ramificationIdx_eq_tameCard`; use `integralClosure.Tame.ringChar_eq_base` and
-- `tameInertiaCard_coprime_ringChar` to obtain coprimality with the supplied prime
-- characteristic.

/-- The base-to-wild index is either unramified in characteristic zero or prime to the base
residue characteristic. -/
@[stacks 0BU6 "base-to-wild tame ramification characteristic dichotomy"]
theorem base_ramificationIdx_coprime_or_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    ringChar (IsLocalRing.maximalIdeal A).ResidueField = 0 ∨
      Nat.Coprime
        (Ideal.ramificationIdx
          (m.under
            (FixedPoints.subalgebra A (integralClosure A L)
              (m.wildInertia Gal(L / K)))) A)
        (ringChar (IsLocalRing.maximalIdeal A).ResidueField) := by
  rcases CharP.char_is_prime_or_zero (IsLocalRing.maximalIdeal A).ResidueField
      (ringChar (IsLocalRing.maximalIdeal A).ResidueField) with hprime | hzero
  · letI : Fact (ringChar (IsLocalRing.maximalIdeal A).ResidueField).Prime := ⟨hprime⟩
    exact Or.inr (base_ramificationIdx_coprime_of_charP (K := K) m _)
  · exact Or.inl hzero

-- Proof strategy: split on the base residue characteristic.  The zero case is the left disjunct;
-- otherwise use that a field's positive characteristic is prime, install its `CharP` instance,
-- and apply `base_ramificationIdx_coprime_of_charP`.

end Wild

end integralClosure.FixedPoints.Ramification
