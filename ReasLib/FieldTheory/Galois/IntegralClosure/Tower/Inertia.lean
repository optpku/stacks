/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower.ResidueField
public import ReasLib.RingTheory.Ideal.Inertia

@[expose] public section

/-!
# Inertia groups in finite Galois towers

This file adds wild- and tame-inertia layers to the inertia-group restriction map.  The ordinary
inertia restriction is owned by the underlying tower file; preservation of the square-ideal
condition and the induced tame quotient are stated in the finite DVR/Galois setting.  Their
surjectivity and numerical divisibility are kept as a separate layer below.

@stack 0BU7
-/

universe u v w z

namespace integralClosure.Tower

section Restriction

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsGalois K L] [FiniteDimensional K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M]
  [IsGalois K M] [FiniteDimensional K M]

/-- Restriction sends upper wild inertia into the wild inertia of the contracted branch. -/
@[stacks 0BU7 "restriction preserves wild inertia"]
theorem restrict_mem_wildInertia
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (sigma : r.wildInertia Gal(M/K)) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma.1 ∈
      (under (A := A) (L := L) (M := M) r).wildInertia Gal(L/K) := sorry
-- Remaining ingredient: functoriality of cotangent inertia in the localized finite DVR tower.
-- Use compatible uniformizers or the associated-graded characterization; contracting `r ^ 2`
-- alone does not give the square of the contracted ideal in a ramified tower.

/-- The homomorphism on wild inertia groups induced by Galois restriction. -/
@[stacks 0BU7 "map on wild inertia groups in a Galois tower"]
noncomputable def wildInertiaHom
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    r.wildInertia Gal(M/K) →*
      (under (A := A) (L := L) (M := M) r).wildInertia Gal(L/K) :=
  ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
      (r.wildInertia Gal(M/K)).subtype).codRestrict _
    (restrict_mem_wildInertia (A := A) (K := K) (L := L) (M := M) r)

/-- The wild-inertia homomorphism is restriction on underlying automorphisms. -/
@[simp, stacks 0BU7 "wild inertia restriction formula"]
theorem wildInertiaHom_apply
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (sigma : r.wildInertia Gal(M/K)) :
    (wildInertiaHom (A := A) (K := K) (L := L) (M := M) r sigma : Gal(L/K)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma.1 := by
  rfl
-- Proof strategy: unfold `wildInertiaHom`; `MonoidHom.codRestrict` changes only the proof of
-- wild-inertia membership, so its coercion is the composite of subgroup inclusion and Galois
-- restriction definitionally.

/-- Upper wild inertia maps into lower wild inertia under the restriction homomorphism on
inertia groups.  This is the subgroup condition needed to descend restriction to tame inertia. -/
@[stacks 0BU7 "wild inertia lies in the pullback under inertia restriction"]
theorem wildInertia_le_comap_inertiaHom
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (r.wildInertia Gal(M/K)).subgroupOf (r.inertia Gal(M/K)) ≤
      Subgroup.comap (inertiaHom (A := A) (K := K) (L := L) (M := M) r)
        (((under (A := A) (L := L) (M := M) r).wildInertia Gal(L/K)).subgroupOf
          ((under (A := A) (L := L) (M := M) r).inertia Gal(L/K))) := by
  intro sigma hsigma
  exact restrict_mem_wildInertia (A := A) (K := K) (L := L) (M := M) r
    ⟨sigma.1, hsigma⟩
-- Proof strategy: use `Subgroup.le_comap`, coerce an upper wild element to upper inertia, and
-- apply `restrict_mem_wildInertia`; identify the resulting ambient automorphism with
-- `inertiaHom` using `inertiaHom_apply`.

/-- The homomorphism on tame inertia induced explicitly by restriction on inertia. -/
@[stacks 0BU7 "map on tame inertia groups in a Galois tower"]
noncomputable def tameInertiaHom
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    r.tameInertia Gal(M/K) →*
      (under (A := A) (L := L) (M := M) r).tameInertia Gal(L/K) :=
  QuotientGroup.map
    ((r.wildInertia Gal(M/K)).subgroupOf (r.inertia Gal(M/K)))
    (((under (A := A) (L := L) (M := M) r).wildInertia Gal(L/K)).subgroupOf
      ((under (A := A) (L := L) (M := M) r).inertia Gal(L/K)))
    (inertiaHom (A := A) (K := K) (L := L) (M := M) r)
    (wildInertia_le_comap_inertiaHom (A := A) (K := K) (L := L) (M := M) r)

/-- Tame-inertia restriction sends the class of an inertia element to the class of its
restriction. -/
@[simp, stacks 0BU7 "tame inertia restriction formula"]
theorem tameInertiaHom_mk
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (sigma : r.inertia Gal(M/K)) :
    tameInertiaHom (A := A) (K := K) (L := L) (M := M) r
        (QuotientGroup.mk sigma) =
      QuotientGroup.mk
        (inertiaHom (A := A) (K := K) (L := L) (M := M) r sigma) := by
  rfl
-- Proof strategy: unfold `tameInertiaHom` and apply `QuotientGroup.map_mk`; the subgroup
-- condition supplied to the quotient map is `wildInertia_le_comap_inertiaHom`.

end Restriction

section Surjectivity

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [fracK : IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [towerAKL : IsScalarTower A K L]
  [galoisKL : IsGalois K L] [finiteKL : FiniteDimensional K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [towerKLM : IsScalarTower K L M] [towerAKM : IsScalarTower A K M]
  [towerALM : IsScalarTower A L M] [galoisKM : IsGalois K M]
  [finiteKM : FiniteDimensional K M]

/-- Restriction maps upper wild inertia onto the wild inertia of the contracted branch. -/
@[stacks 0BU7 "surjectivity on wild inertia in a Galois tower"]
theorem map_wildInertia_eq
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (r.wildInertia Gal(M/K)) =
      (under (A := A) (L := L) (M := M) r).wildInertia Gal(L/K) := sorry
-- Remaining ingredient: wild inertia is the normal residue-characteristic Sylow subgroup of
-- inertia, and is trivial in residue characteristic zero. Together with
-- `inertiaHom_surjective`, its Sylow description gives surjectivity as in Stacks 0BU7.

/-- The induced homomorphism from upper to lower wild inertia is surjective. -/
@[stacks 0BU7 "surjective wild-inertia restriction"]
theorem wildInertiaHom_surjective
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    Function.Surjective
      (wildInertiaHom (A := A) (K := K) (L := L) (M := M) r) := by
  intro sigma
  have hsigma : sigma.1 ∈ Subgroup.map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (r.wildInertia Gal(M/K)) := by
    rw [map_wildInertia_eq (A := A) (K := K) (L := L) (M := M) r]
    exact sigma.property
  obtain ⟨tau, htau, htausigma⟩ := hsigma
  exact ⟨⟨tau, htau⟩, Subtype.ext htausigma⟩
-- Proof strategy: translate `map_wildInertia_eq` into surjectivity of the codomain-restricted
-- map, using `wildInertiaHom_apply` to identify its ambient value with Galois restriction.

/-- Restriction from upper tame inertia onto lower tame inertia is surjective. -/
@[stacks 0BU7 "surjective tame-inertia restriction"]
theorem tameInertiaHom_surjective
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    Function.Surjective
      (tameInertiaHom (A := A) (K := K) (L := L) (M := M) r) := by
  apply QuotientGroup.map_surjective_of_surjective
  exact (QuotientGroup.mk'_surjective _).comp
    (inertiaHom_surjective (A := A) (K := K) (L := L) (M := M) r)
-- Proof strategy: apply `QuotientGroup.map_surjective_of_surjective`. Surjectivity after the
-- lower quotient projection follows from `inertiaHom_surjective` and
-- `QuotientGroup.mk'_surjective`; the induced-map formula is `tameInertiaHom_mk`.

/-- In a finite Galois tower, the order of lower tame inertia divides the order of upper tame
inertia. -/
@[stacks 0BU7 "divisibility of tame inertia orders in a Galois tower"]
theorem tameInertiaCard_dvd
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    Nat.card ((under (A := A) (L := L) (M := M) r).tameInertia Gal(L/K)) ∣
      Nat.card (r.tameInertia Gal(M/K)) := by
  exact Subgroup.card_dvd_of_surjective
    (tameInertiaHom (A := A) (K := K) (L := L) (M := M) r)
    (tameInertiaHom_surjective (A := A) (K := K) (L := L) (M := M) r)
-- Proof strategy: apply `Subgroup.card_dvd_of_surjective` to `tameInertiaHom` and
-- `tameInertiaHom_surjective`; finiteness of both quotient groups comes from the finite Galois
-- groups.

include fracK towerAKL galoisKL finiteKL towerKLM towerAKM towerALM galoisKM finiteKM in
/-- The ramification index in the lower finite Galois extension divides the ramification index
in the upper extension.  No branch ideal is needed because `ramificationIdxIn` is already the
branch-independent Galois invariant. -/
@[stacks 0BU7 "divisibility of ramification indices in a Galois tower"]
theorem ramificationIdxIn_dvd :
    Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L) ∣
      Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A M) := by
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  letI : IsScalarTower A (integralClosure A L) (integralClosure A M) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      ((towerMap (A := A) (L := L) (M := M)).commutes x).symm
  letI : IsDedekindDomain (integralClosure A L) :=
    integralClosure.isDedekindDomain A K L
  letI : Module.IsTorsionFree (integralClosure A L) (integralClosure A M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y h
      apply Subtype.ext
      exact (algebraMap L M).injective (congrArg Subtype.val h))
  letI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  letI : IsFractionRing (integralClosure A M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K M (integralClosure A M)
  letI : IsGaloisGroup Gal(L/K) A (integralClosure A L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) A (integralClosure A L) K L
  letI : IsGaloisGroup Gal(M/K) A (integralClosure A M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K) A (integralClosure A M) K M
  letI : Module.IsTorsionFree A M := Module.IsTorsionFree.trans_faithfulSMul A K M
  obtain ⟨r⟩ := (inferInstance :
    Nonempty ((IsLocalRing.maximalIdeal A).primesOver (integralClosure A M)))
  let q := r.1.under (integralClosure A L)
  letI : r.1.LiesOver q := Ideal.over_under r.1
  letI : q.LiesOver (IsLocalRing.maximalIdeal A) :=
    Ideal.LiesOver.tower_bot r.1 q (IsLocalRing.maximalIdeal A)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal A) q Gal(L/K),
    Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal A) r.1 Gal(M/K)]
  exact Ideal.ramificationIdx_below_dvd q r.1
-- Use a prime above the base maximal ideal and its contraction. The canonical tower map is
-- injective, so the upper closure is flat over the lower Dedekind domain. Branch-independent
-- Galois indices then reduce the claim to `Ideal.ramificationIdx_below_dvd`.

end Surjectivity

end integralClosure.Tower
