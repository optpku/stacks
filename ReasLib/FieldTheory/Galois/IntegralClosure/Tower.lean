/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReasLib.Algebra.Group.Action.Stabilizer
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField
public import ReasLib.FieldTheory.Galois.Tower

/-!
# Integral-closure tower maps

The reusable tower map, named tower algebra, branch residue-separability predicate, and
ramification-index specification are shared by the Chapter 15 branch statements.

@stack 0BSX
-/

@[expose] public section

open scoped Pointwise

universe u v w z

namespace integralClosure.Tower

section Map

variable {A : Type u} {L : Type v} {M : Type w}
variable [CommRing A] [Field L] [Algebra A L]
variable [Field M] [Algebra L M] [Algebra A M] [IsScalarTower A L M]

/-- The canonical map between integral closures induced by a field tower. -/
@[stacks 0BSX "integral-closure map in a Galois tower"]
def towerMap : integralClosure A L →ₐ[A] integralClosure A M :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

/-- The named algebra structure on the two integral closures induced by `towerMap`.

This is deliberately a definition rather than a global instance: an `Algebra` structure
between two integral-closure carriers depends on the chosen ambient tower, and installing it
globally can create instance diamonds. -/
@[reducible, stacks 0BSX "algebra structure on an integral-closure tower"]
noncomputable def algebra : Algebra (integralClosure A L) (integralClosure A M) :=
  (towerMap (A := A) (L := L) (M := M)).toAlgebra

/-- The tower map evaluates on an integral element as the ambient field inclusion. -/
@[simp, stacks 0BSX "integral-closure tower map evaluation"]
theorem towerMap_apply (x : integralClosure A L) :
    (towerMap (A := A) (L := L) (M := M) x : M) = algebraMap L M (x : L) := by
  rfl
-- Proof strategy: unfold `towerMap` and `IsScalarTower.AlgHom.mapIntegralClosure`; extensionality
-- in the integral-closure subtype reduces the claim to the ambient field inclusion formula.

/-- With the named tower algebra installed, its algebra map is the explicit `towerMap`. -/
@[simp, stacks 0BSX "algebra map of an integral-closure tower"]
theorem algebraMap_apply (x : integralClosure A L) :
    -- Local instance justification (defeq pin): install the named `towerMap.toAlgebra` whose map is compared here.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    algebraMap (integralClosure A L) (integralClosure A M) x =
      towerMap (A := A) (L := L) (M := M) x := by
  rfl
-- Proof strategy: unfold `algebra` and the `AlgHom.toAlgebra` algebra map; the resulting bundled
-- homomorphism is definitionally `towerMap`, so conclude by extensionality of the subtype.

/-- The named tower algebra is compatible with the ambient field tower. -/
@[stacks 0BSX "scalar tower for integral closures in a field tower"]
theorem isScalarTower :
    -- Local instance justification (defeq pin): install `towerMap.toAlgebra` so its scalar tower agrees with `under`.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    IsScalarTower (integralClosure A L) (integralClosure A M) M := by
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
-- Proof strategy: apply `IsScalarTower.of_algebraMap_eq`; after coercing to `M`, rewrite the
-- lower algebra map with `algebraMap_apply` and `towerMap_apply`, then use the ambient scalar
-- tower `A → L → M`.

/-- Contraction of an ideal of the upper integral closure along the canonical tower map. -/
@[stacks 0BSX "contraction along an integral-closure tower"]
abbrev under (r : Ideal (integralClosure A M)) : Ideal (integralClosure A L) :=
  r.comap (towerMap (A := A) (L := L) (M := M)).toRingHom

/-- Membership in the tower contraction is computed by the explicit tower map. -/
@[simp, stacks 0BSX "membership in an integral-closure tower contraction"]
theorem mem_under_iff (r : Ideal (integralClosure A M)) (x : integralClosure A L) :
    x ∈ under (A := A) (L := L) (M := M) r ↔
      towerMap (A := A) (L := L) (M := M) x ∈ r := by
  rfl
-- Proof strategy: unfold `under` and apply `Ideal.mem_comap`; its right-hand side is exactly
-- evaluation by `towerMap.toRingHom`.

/-- The explicit contraction agrees with `Ideal.under` after installing the named tower
algebra. -/
@[simp, stacks 0BSX "canonical under ideal in an integral-closure tower"]
theorem under_eq (r : Ideal (integralClosure A M)) :
    -- Local instance justification (defeq pin): install `towerMap.toAlgebra` for the contraction comparison.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    under (A := A) (L := L) (M := M) r = r.under (integralClosure A L) := by
  rfl
-- Proof strategy: unfold `under` and `Ideal.under`; prove the two comap ring homomorphisms equal
-- by extensionality and `algebraMap_apply`.

/-- Separability of the residue-field extension on a branch of an integral-closure tower.

The pair-dependent algebra on the integral closures and its lying-over witness are deliberately
scoped inside this predicate, so downstream statements do not need to install either instance. -/
@[stacks 0BSX "residue separability on an integral-closure tower branch"]
def branchResidueSeparable (r : Ideal (integralClosure A M)) [r.IsPrime] : Prop :=
  -- Local instance justification (defeq pin): pin the contracted branch to the named `towerMap.toAlgebra`.
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  -- Local instance justification (defeq pin): retain the contracted-branch lying-over witness used by the residue predicate.
  letI : r.LiesOver (under (A := A) (L := L) (M := M) r) := Ideal.over_under r
  @Algebra.IsSeparable
    (under (A := A) (L := L) (M := M) r).ResidueField r.ResidueField _ _
    (Ideal.ResidueField.algebraOfLiesOver
      (under (A := A) (L := L) (M := M) r) r)

/-- The ramification index of a branch over the lower integral closure in a field tower.

The chosen integral-closure algebra remains internal to the definition, matching the canonical
map used by `under`. -/
@[stacks 0BSX "ramification index on an integral-closure tower branch"]
noncomputable def branchRamificationIdx (r : Ideal (integralClosure A M)) : ℕ :=
  -- Local instance justification (defeq pin): pin the ramification expression to the named integral-closure tower algebra.
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  r.ramificationIdx (integralClosure A L)

/-- With the named tower algebra installed, branch residue separability is the usual
`Algebra.IsSeparable` predicate for the contracted residue-field extension. -/
@[simp, stacks 0BSX "branch residue separability specification"]
theorem branchResidueSeparable_iff (r : Ideal (integralClosure A M)) [r.IsPrime] :
    -- Local instance justification (defeq pin): install the named tower algebra for the residue-separability specification.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    branchResidueSeparable (A := A) (L := L) (M := M) r ↔
      @Algebra.IsSeparable
        (r.under (integralClosure A L)).ResidueField r.ResidueField _ _
        (Ideal.ResidueField.algebraOfLiesOver (r.under (integralClosure A L)) r) := by
  rfl
-- Proof strategy: unfold `branchResidueSeparable`, rewrite the contracted ideal with `under_eq`,
-- and use proof irrelevance for the locally installed `LiesOver` and residue-field algebra
-- structures.

/-- With the named tower algebra installed, `branchRamificationIdx` is Mathlib's ramification
index over the lower integral closure. -/
@[simp, stacks 0BSX "branch ramification index specification"]
theorem branchRamificationIdx_eq (r : Ideal (integralClosure A M)) :
    -- Local instance justification (defeq pin): install the named tower algebra for the ramification specification.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    branchRamificationIdx (A := A) (L := L) (M := M) r =
      r.ramificationIdx (integralClosure A L) := by
  rfl
-- Proof strategy: unfold `branchRamificationIdx` and `algebra`; both sides then use the same
-- explicitly installed `towerMap.toAlgebra`, so the equality is definitional.

/-- The upper Galois action commutes with the named lower integral-closure algebra. -/
private theorem tower_smulCommClass :
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    SMulCommClass Gal(M/L) (integralClosure A L) (integralClosure A M) := by
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  exact ⟨fun τ x y => by
    apply Subtype.ext
    change τ (algebraMap L M (x : L) * (y : M)) =
      algebraMap L M (x : L) * τ (y : M)
    rw [map_mul, τ.commutes]⟩

/-- Fixed integral elements of a Galois extension come from the lower integral closure. -/
private theorem tower_isInvariant [IsGalois L M] :
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    Algebra.IsInvariant (integralClosure A L) (integralClosure A M) Gal(M/L) := by
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (x : M)).2
    (fun τ => congrArg Subtype.val (hx τ))
  have hyint : IsIntegral A y := by
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom A L M)
      (algebraMap L M).injective).mp
    change IsIntegral A (algebraMap L M y)
    rw [hy]
    exact x.property
  exact ⟨⟨y, hyint⟩, Subtype.ext hy⟩

/-- The Galois action on a discrete integral closure is continuous for the Krull topology. -/
private theorem tower_continuousSMul [Algebra.IsIntegral L M] :
    letI : TopologicalSpace (integralClosure A M) := ⊥
    ContinuousSMul Gal(M/L) (integralClosure A M) := by
  letI : TopologicalSpace (integralClosure A M) := ⊥
  letI : DiscreteTopology (integralClosure A M) := ⟨rfl⟩
  apply (continuousSMul_iff_stabilizer_isOpen).2
  intro x
  convert! stabilizer_isOpen_of_isIntegral (K := L) (x : M) using 1
  ext τ
  change (τ • x = x) ↔ (τ (x : M) = (x : M))
  exact Subtype.ext_iff

end Map

section Restriction

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Normal K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M]

/-- The tower inclusion intertwines the upper action with normal restriction. -/
private theorem towerMap_restrict_smul (σ : Gal(M/K)) (x : integralClosure A L) :
    towerMap (A := A) (L := L) (M := M)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ • x) =
      σ • towerMap (A := A) (L := L) (M := M) x := by
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ L (x : L)

/-- The contraction of a conjugated ideal is the conjugate of its contraction. -/
@[stacks 0BSX "contraction and Galois restriction"]
theorem under_smul (σ : Gal(M/K)) (r : Ideal (integralClosure A M)) :
    under (A := A) (L := L) (M := M) (σ • r) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ •
        under (A := A) (L := L) (M := M) r := by
  ext x
  simp only [mem_under_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    towerMap_restrict_smul]
-- Proof strategy: ext on lower integral elements, rewrite membership by `mem_under_iff` and
-- pointwise ideal transport, and use `towerMap_apply` together with
-- `AlgEquiv.restrictNormal_commutes` to identify the two ambient actions.

/-- Restricting an automorphism that stabilizes an upper ideal gives an automorphism
stabilizing its contraction. -/
@[stacks 0BSX "restriction preserves decomposition groups"]
theorem restrict_mem_stabilizer (r : Ideal (integralClosure A M))
    (σ : MulAction.stabilizer Gal(M/K) r) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 ∈
      MulAction.stabilizer Gal(L/K) (under (A := A) (L := L) (M := M) r) := by
  change AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 •
      under (A := A) (L := L) (M := M) r = _
  rw [← under_smul, σ.property]
-- Proof strategy: unfold membership in `MulAction.stabilizer`, rewrite the restricted action by
-- `under_smul`, and finish with the upper stabilizer equality `σ.2`.

/-- The homomorphism on decomposition groups induced by Galois restriction. -/
@[stacks 0BSX "map on decomposition groups in a Galois tower"]
noncomputable def decompositionHom (r : Ideal (integralClosure A M)) :
    MulAction.stabilizer Gal(M/K) r →*
      MulAction.stabilizer Gal(L/K) (under (A := A) (L := L) (M := M) r) :=
  ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
      (MulAction.stabilizer Gal(M/K) r).subtype).codRestrict _
    (restrict_mem_stabilizer (A := A) (K := K) (L := L) (M := M) r)

/-- The decomposition-group homomorphism is restriction on underlying automorphisms. -/
@[simp, stacks 0BSX "decomposition-group restriction formula"]
theorem decompositionHom_apply (r : Ideal (integralClosure A M))
    (σ : MulAction.stabilizer Gal(M/K) r) :
    (decompositionHom (A := A) (K := K) (L := L) (M := M) r σ : Gal(L/K)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 := by
  rfl
-- Proof strategy: unfold `decompositionHom`; coercion through `MonoidHom.codRestrict` preserves
-- the value of the composed restriction homomorphism definitionally.

/-- Restricting an upper inertia element gives an inertia element at the contracted ideal. -/
@[stacks 0BSX "restriction preserves inertia groups"]
theorem restrict_mem_inertia (r : Ideal (integralClosure A M))
    (σ : r.inertia Gal(M/K)) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 ∈
      (under (A := A) (L := L) (M := M) r).inertia Gal(L/K) := by
  intro x
  change towerMap (A := A) (L := L) (M := M)
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 • x - x) ∈ r
  rw [map_sub, towerMap_restrict_smul]
  exact σ.property _
-- Proof strategy: use `AddSubgroup.mem_inertia`. For each lower integral element, rewrite
-- membership in `under r` with `mem_under_iff`; `towerMap_apply` and
-- `AlgEquiv.restrictNormal_commutes` turn the required difference into the upper inertia
-- hypothesis `σ.2` evaluated at its image under `towerMap`.

/-- The homomorphism on inertia groups induced by Galois restriction. -/
@[stacks 0BSX "map on inertia groups in a Galois tower"]
noncomputable def inertiaHom (r : Ideal (integralClosure A M)) :
    r.inertia Gal(M/K) →*
      (under (A := A) (L := L) (M := M) r).inertia Gal(L/K) :=
  ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
      (r.inertia Gal(M/K)).subtype).codRestrict _
    (restrict_mem_inertia (A := A) (K := K) (L := L) (M := M) r)

/-- The inertia-group homomorphism is restriction on underlying automorphisms. -/
@[simp, stacks 0BSX "inertia-group restriction formula"]
theorem inertiaHom_apply (r : Ideal (integralClosure A M)) (σ : r.inertia Gal(M/K)) :
    (inertiaHom (A := A) (K := K) (L := L) (M := M) r σ : Gal(L/K)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 := by
  rfl
-- Proof strategy: unfold `inertiaHom`; the codomain restriction changes only the proof of
-- subgroup membership, so the ambient automorphism is definitionally the restricted one.

end Restriction

section Surjectivity

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M]
  [IsGalois K M]

/-- Restriction maps the decomposition group at an upper prime onto the decomposition
group at its contraction. -/
@[stacks 0BSX "surjectivity on decomposition groups in a Galois tower"]
theorem map_stabilizer_eq (r : Ideal (integralClosure A M)) [r.IsPrime] :
    Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (MulAction.stabilizer Gal(M/K) r) =
      MulAction.stabilizer Gal(L/K)
        (under (A := A) (L := L) (M := M) r) := by
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  -- Use the named algebra so contractions and the lower scalar action use the same map.
  letI : Algebra (integralClosure A L) (integralClosure A M) :=
    algebra (A := A) (L := L) (M := M)
  letI : SMulCommClass Gal(M/L) (integralClosure A L) (integralClosure A M) :=
    tower_smulCommClass
  letI : Algebra.IsInvariant (integralClosure A L) (integralClosure A M) Gal(M/L) :=
    tower_isInvariant
  -- Apply the profinite orbit theorem to the canonical action on the discrete ring.
  letI : TopologicalSpace (integralClosure A M) := ⊥
  letI : DiscreteTopology (integralClosure A M) := ⟨rfl⟩
  letI : ContinuousSMul Gal(M/L) (integralClosure A M) := tower_continuousSMul
  refine Subgroup.map_stabilizer_eq_of_surjective_of_fiber
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
    (under (A := A) (L := L) (M := M)) r
    (fun σ I => under_smul σ I)
    (FieldExtension.restrictNormalHomSurjective K L M) ?_
  intro σ hσ
  have hcontr : (σ • r).under (integralClosure A L) = r.under (integralClosure A L) := hσ
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := integralClosure A L) (B := integralClosure A M) (G := Gal(M/L))
    (σ • r) r hcontr
  have hk : FieldExtension.galRestrictScalarsHom K L M τ ∈
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker := by
    rw [← FieldExtension.galRestrictScalarsHom_range_eq_restrictNormalHom_ker K L M]
    exact ⟨τ, rfl⟩
  refine ⟨⟨FieldExtension.galRestrictScalarsHom K L M τ, hk⟩, ?_⟩
  have hact (I : Ideal (integralClosure A M)) :
      FieldExtension.galRestrictScalarsHom K L M τ • I = τ • I := by
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [hact]
  exact hτ.symm
-- Proof strategy: apply `Subgroup.map_stabilizer_eq_of_surjective_of_fiber` to Galois
-- restriction and the contraction map. Equivariance is `under_smul`, and surjectivity is
-- `FieldExtension.restrictNormalHomSurjective`. For the fiber correction, apply
-- Mathlib's profinite invariant orbit theorem over the lower integral closure, then identify
-- `Gal(M/L)` with the kernel of restriction via
-- `FieldExtension.galRestrictScalarsHom_range_eq_restrictNormalHom_ker`.

/-- The induced homomorphism from the upper decomposition group to the lower one is
surjective. -/
@[stacks 0BSX "surjective decomposition-group restriction"]
theorem decompositionHom_surjective (r : Ideal (integralClosure A M)) [r.IsPrime] :
    Function.Surjective (decompositionHom (A := A) (K := K) (L := L) (M := M) r) := by
  intro σ
  have hσ : σ.1 ∈ Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (MulAction.stabilizer Gal(M/K) r) := by
    rw [map_stabilizer_eq (A := A) (K := K) (L := L) (M := M) r]
    exact σ.property
  obtain ⟨τ, hτ, hτσ⟩ := hσ
  exact ⟨⟨τ, hτ⟩, Subtype.ext hτσ⟩
-- Proof strategy: rewrite surjectivity of the codomain-restricted homomorphism as equality of
-- the image subgroup, then apply `map_stabilizer_eq` and use `decompositionHom_apply` to identify
-- the ambient maps.

/-- Restriction maps the inertia group at an upper prime onto the inertia group at its
contraction. -/
@[stacks 0BSX "surjectivity on inertia groups in a Galois tower"]
theorem map_inertia_eq (r : Ideal (integralClosure A M)) [r.IsPrime] :
    Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (r.inertia Gal(M/K)) =
      (under (A := A) (L := L) (M := M) r).inertia Gal(L/K) := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact restrict_mem_inertia r ⟨σ, hσ⟩
  · intro σ hσ
    have hσD := Ideal.inertia_le_stabilizer
      (M := Gal(L/K)) (under (A := A) (L := L) (M := M) r) hσ
    obtain ⟨τ, hτ⟩ := decompositionHom_surjective
      (A := A) (K := K) (L := L) (M := M) r ⟨σ, hσD⟩
    have hτrestrict : AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L τ.1 = σ :=
      congrArg Subtype.val hτ
    letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    -- The kernel action fixes the lower integral closure through the named tower algebra.
    letI : Algebra (integralClosure A L) (integralClosure A M) :=
      algebra (A := A) (L := L) (M := M)
    letI : SMulCommClass Gal(M/L) (integralClosure A L) (integralClosure A M) :=
      tower_smulCommClass
    letI : Algebra.IsInvariant (integralClosure A L) (integralClosure A M) Gal(M/L) :=
      tower_isInvariant
    letI : TopologicalSpace (integralClosure A M) := ⊥
    letI : DiscreteTopology (integralClosure A M) := ⟨rfl⟩
    letI : ContinuousSMul Gal(M/L) (integralClosure A M) := tower_continuousSMul
    let q := under (A := A) (L := L) (M := M) r
    letI : r.LiesOver q := Ideal.over_under r
    -- The lifted stabilizer element fixes the lower quotient because its restriction is inertia.
    let α : (integralClosure A M ⧸ r) ≃+* (integralClosure A M ⧸ r) :=
      Ideal.quotientEquiv r r
        (MulSemiringAction.toRingAut Gal(M/K) (integralClosure A M) τ.1) τ.property.symm
    have hα (x : integralClosure A M) :
        α (Ideal.Quotient.mk r x) = Ideal.Quotient.mk r (τ.1 • x) := rfl
    have hfix (b : integralClosure A L) :
        α (Ideal.Quotient.mk r (towerMap (A := A) (L := L) (M := M) b)) =
          Ideal.Quotient.mk r (towerMap (A := A) (L := L) (M := M) b) := by
      rw [hα]
      apply Ideal.Quotient.eq.mpr
      have hbase :
          AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L τ.1 • b - b ∈ q := by
        rw [hτrestrict]
        exact hσ b
      change towerMap (A := A) (L := L) (M := M)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L τ.1 • b - b) ∈ r at hbase
      rwa [map_sub, towerMap_restrict_smul] at hbase
    let αB : (integralClosure A M ⧸ r) ≃ₐ[integralClosure A L ⧸ q]
        (integralClosure A M ⧸ r) :=
      AlgEquiv.ofRingEquiv (f := α) (by
        intro b
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact hfix b)
    obtain ⟨ρ, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := Gal(M/L)) q r αB
    have hρact (x : integralClosure A M) :
        Ideal.Quotient.mk r (ρ.1 • x) = Ideal.Quotient.mk r (τ.1 • x) :=
      DFunLike.congr_fun hρ (Ideal.Quotient.mk r x)
    let κ := FieldExtension.galRestrictScalarsHom K L M ρ.1
    have hκ : AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L κ = 1 := by
      change κ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker
      rw [← FieldExtension.galRestrictScalarsHom_range_eq_restrictNormalHom_ker K L M]
      exact ⟨ρ.1, rfl⟩
    refine ⟨κ⁻¹ * τ.1, ?_, ?_⟩
    · intro x
      have hd : τ.1 • x - ρ.1 • x ∈ r := Ideal.Quotient.eq.mp (hρact x).symm
      have hd' := Ideal.smul_mem_pointwise_smul ρ.1⁻¹ _ r hd
      rw [show ρ.1⁻¹ • r = r from
        (MulAction.stabilizer Gal(M/L) r).inv_mem ρ.property] at hd'
      change ρ.1⁻¹ • (τ.1 • x) - x ∈ r
      simpa only [smul_sub, inv_smul_smul] using hd'
    · rw [map_mul, map_inv, hκ, inv_one, one_mul, hτrestrict]
-- Proof strategy: the forward inclusion is `restrict_mem_inertia`. For the reverse inclusion,
-- lift a lower inertia element through `decompositionHom_surjective`. Its upper residue action
-- fixes the lower quotient ring. Mathlib's profinite quotient-stabilizer surjectivity supplies a
-- `Gal(M/L)` correction with the same upper quotient action. Multiplying by its inverse kills
-- that action and preserves the prescribed restriction, giving an upper inertia element.

/-- The induced homomorphism from the upper inertia group to the lower one is surjective. -/
@[stacks 0BSX "surjective inertia-group restriction"]
theorem inertiaHom_surjective (r : Ideal (integralClosure A M)) [r.IsPrime] :
    Function.Surjective (inertiaHom (A := A) (K := K) (L := L) (M := M) r) := by
  intro σ
  have hσ : σ.1 ∈ Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (r.inertia Gal(M/K)) := by
    rw [map_inertia_eq (A := A) (K := K) (L := L) (M := M) r]
    exact σ.property
  obtain ⟨τ, hτ, hτσ⟩ := hσ
  exact ⟨⟨τ, hτ⟩, Subtype.ext hτσ⟩
-- Proof strategy: translate `map_inertia_eq` from ambient subgroup images to surjectivity of the
-- codomain-restricted `inertiaHom`, using `inertiaHom_apply` for the coercion-level formula.

end Surjectivity

end integralClosure.Tower
