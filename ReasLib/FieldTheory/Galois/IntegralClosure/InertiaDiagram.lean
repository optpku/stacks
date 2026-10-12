/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Affine
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.ResidueField
public import ReasLib.Topology.Category.ProfiniteGrp.InertiaDiagram

@[expose] public section

open scoped Pointwise
open AlgebraicGeometry AlgebraicGeometry.Scheme.FunctionFieldExtension
open CategoryTheory EtaleFundamentalGroup Ideal Ideal.ResidueField.Invariant InfiniteGalois
open IsLocalRing

universe u

namespace integralClosure

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
variable [IsIntegral (Spec (CommRingCat.of A))]

/-- The scalar action of `A` on the separable closure of the function field of `Spec A`. -/
noncomputable instance algebraSeparableClosure :
    Algebra A (SeparableClosure (Spec (CommRingCat.of A)).functionField) :=
  RingHom.toAlgebra
    ((algebraMap (Spec (CommRingCat.of A)).functionField
        (SeparableClosure (Spec (CommRingCat.of A)).functionField)).comp
      (algebraMap A (Spec (CommRingCat.of A)).functionField))

/-- The canonical maps through the function field form a scalar tower with its separable closure. -/
instance isScalarTowerSeparableClosure :
    IsScalarTower A (Spec (CommRingCat.of A)).functionField
      (SeparableClosure (Spec (CommRingCat.of A)).functionField) := sorry

variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable {Ksep : Type u} [Field Ksep] [Algebra A Ksep] [Algebra K Ksep]
  [IsScalarTower A K Ksep] [IsGalois K Ksep]

/-- The inertia subgroup is compact. -/
noncomputable instance instCompactSpace_inertia
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] :
    CompactSpace (m.inertia (Ksep ≃ₐ[K] Ksep)) := sorry

/-- The decomposition group is compact. -/
noncomputable instance instCompactSpace_decomposition
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] :
    CompactSpace (MulAction.stabilizer (Ksep ≃ₐ[K] Ksep) m) := sorry

/-- The inertia subgroup viewed as a profinite group. -/
noncomputable def inertiaProfinite (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (m.inertia (Ksep ≃ₐ[K] Ksep))

/-- The decomposition group viewed as a profinite group. -/
noncomputable def decompositionProfinite (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (MulAction.stabilizer (Ksep ≃ₐ[K] Ksep) m)

/-- The residue field of a maximal integral-closure ideal is an algebra over the base residue field. -/
noncomputable instance instAlgebra_residueField
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] :
    Algebra (maximalIdeal A).ResidueField m.ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) m

/-- The separable residue-field extension has a canonical Galois structure. -/
noncomputable instance instIsGalois_kappaSep
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    IsGalois (maximalIdeal A).ResidueField
      (separableClosure (maximalIdeal A).ResidueField m.ResidueField) := sorry

/-- The residue field extension is normal over the residue field of the base. -/
noncomputable instance instNormal_residueField
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    Normal (maximalIdeal A).ResidueField m.ResidueField := sorry

/-- The residue action homomorphism from the decomposition group. -/
noncomputable def residueGaloisHom (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    MulAction.stabilizer (Ksep ≃ₐ[K] Ksep) m →*
      Gal(separableClosure (maximalIdeal A).ResidueField m.ResidueField /
        (maximalIdeal A).ResidueField) :=
  (AlgEquiv.restrictNormalHom
      (separableClosure (maximalIdeal A).ResidueField m.ResidueField)).comp
    (stabilizerHom (Ksep ≃ₐ[K] Ksep) (maximalIdeal A) m)

/-- Applying the residue action is restriction of the induced residue automorphism. -/
theorem residueGaloisHom_apply (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A]
    (σ : MulAction.stabilizer (Ksep ≃ₐ[K] Ksep) m)
    (x : separableClosure (maximalIdeal A).ResidueField m.ResidueField) :
    residueGaloisHom K m σ x =
      AlgEquiv.restrictNormalHom
        (separableClosure (maximalIdeal A).ResidueField m.ResidueField)
        (stabilizerHom (Ksep ≃ₐ[K] Ksep) (maximalIdeal A) m σ) x := sorry

/-- The residue action homomorphism is continuous for the profinite topologies. -/
noncomputable def residueGaloisContinuousHom
    (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    MulAction.stabilizer (Ksep ≃ₐ[K] Ksep) m →ₜ*
      Gal(separableClosure (maximalIdeal A).ResidueField m.ResidueField /
        (maximalIdeal A).ResidueField) where
  toFun := residueGaloisHom K m
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- In the normal-local function-field setting, the residue action is surjective. -/
theorem residueGaloisHom_surjective
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    Function.Surjective
      (residueGaloisHom (Spec (CommRingCat.of A)).functionField m) := sorry

/-- In the normal-local function-field setting, the residue-action kernel is inertia. -/
theorem residueGaloisHom_ker
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    (residueGaloisHom (Spec (CommRingCat.of A)).functionField m).ker =
      (m.inertia
          (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
            (Spec (CommRingCat.of A)).functionField]
            SeparableClosure (Spec (CommRingCat.of A)).functionField)).subgroupOf
        (MulAction.stabilizer
          (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
            (Spec (CommRingCat.of A)).functionField]
            SeparableClosure (Spec (CommRingCat.of A)).functionField) m) := sorry

end integralClosure

namespace EtaleFundamentalGroup

open integralClosure

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable {Ksep : Type u} [Field Ksep] [Algebra A Ksep] [Algebra K Ksep]
  [IsScalarTower A K Ksep] [IsGalois K Ksep]

/-- A normal intermediate field inherits the Galois structure needed for restriction. -/
noncomputable instance instIsGalois_unramified (M : IntermediateField K Ksep) [Normal K M] :
    IsGalois K M := sorry

/-- Restriction from the full Galois group to a normal intermediate field. -/
noncomputable def restrictUnramifiedHom (M : IntermediateField K Ksep) [Normal K M] :
    (Ksep ≃ₐ[K] Ksep) →* Gal(M/K) :=
  AlgEquiv.restrictNormalHom M

/-- Restriction to a normal intermediate field agrees with canonical restriction. -/
theorem restrictUnramifiedHom_eq_restrictNormalHom
    (M : IntermediateField K Ksep) [Normal K M] :
    restrictUnramifiedHom K M = AlgEquiv.restrictNormalHom M := sorry

/-- Restriction to a normal intermediate field as a continuous homomorphism. -/
noncomputable def restrictUnramifiedContinuousHom
    (M : IntermediateField K Ksep) [Normal K M] :
    (Ksep ≃ₐ[K] Ksep) →ₜ* Gal(M/K) where
  toFun := restrictUnramifiedHom K M
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- The kernel of restriction to the maximal unramified extension is the closed normal
closure of inertia. -/
theorem restrictUnramifiedHom_ker
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    (restrictUnramifiedHom (Spec (CommRingCat.of A)).functionField
        (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)).ker =
      (Subgroup.normalClosure
        (m.inertia
            (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
              (Spec (CommRingCat.of A)).functionField]
              SeparableClosure (Spec (CommRingCat.of A)).functionField) :
          Set
            (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
              (Spec (CommRingCat.of A)).functionField]
              SeparableClosure (Spec (CommRingCat.of A)).functionField))).topologicalClosure :=
  sorry

/-- Inertia embeds into the decomposition group as a profinite homomorphism. -/
noncomputable def inertiaToDecomposition (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] :
    inertiaProfinite K m ⟶ decompositionProfinite K m :=
  ProfiniteGrp.ofHom
    { toFun := Subgroup.inclusion (Ideal.inertia_le_stabilizer m)
      map_one' := sorry
      map_mul' := sorry
      continuous_toFun := sorry }

/-- The decomposition group embeds into the full Galois group as a profinite homomorphism. -/
noncomputable def decompositionToGal (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] :
    decompositionProfinite K m ⟶ profiniteGalGrp K Ksep :=
  ProfiniteGrp.ofHom
    { toFun := fun σ ↦ σ.val
      map_one' := sorry
      map_mul' := sorry
      continuous_toFun := sorry }

/-- The residue homomorphism as a profinite arrow. -/
noncomputable def residueGaloisHomProfinite (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    decompositionProfinite K m ⟶
      profiniteGalGrp (maximalIdeal A).ResidueField
        (separableClosure (maximalIdeal A).ResidueField m.ResidueField) :=
  ProfiniteGrp.ofHom (residueGaloisContinuousHom K m)

/-- Restriction to a normal intermediate field as a profinite arrow. -/
noncomputable def restrictUnramifiedHomProfinite (M : IntermediateField K Ksep) [Normal K M] :
    profiniteGalGrp K Ksep ⟶ profiniteGalGrp K M :=
  ProfiniteGrp.ofHom (restrictUnramifiedContinuousHom K M)

/-- The trivial profinite arrow from inertia to the residue Galois group. -/
noncomputable def inertiaToResidueTrivial (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    [m.LiesOver (maximalIdeal A)] [IsIntegrallyClosed A] :
    inertiaProfinite K m ⟶
      profiniteGalGrp (maximalIdeal A).ResidueField
        (separableClosure (maximalIdeal A).ResidueField m.ResidueField) :=
  ProfiniteGrp.ofHom
    { toFun := fun _ ↦ 1
      map_one' := sorry
      map_mul' := sorry
      continuous_toFun := sorry }

/-- The residue Galois group maps to the Galois group of the maximal unramified extension. -/
noncomputable def residueToUnramifiedHom
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    Gal(separableClosure (maximalIdeal A).ResidueField m.ResidueField /
        (maximalIdeal A).ResidueField) →*
      Gal(maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX /
        (Spec (CommRingCat.of A)).functionField) where
  toFun σ :=
    restrictUnramifiedHom (Spec (CommRingCat.of A)).functionField
      (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)
      (Function.invFun
        (residueGaloisHom (Spec (CommRingCat.of A)).functionField m) σ).val
  map_one' := sorry
  map_mul' := sorry

/-- The residue-to-unramified homomorphism as a continuous homomorphism. -/
noncomputable def residueToUnramifiedContinuousHom
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    Gal(separableClosure (maximalIdeal A).ResidueField m.ResidueField /
        (maximalIdeal A).ResidueField) →ₜ*
      Gal(maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX /
        (Spec (CommRingCat.of A)).functionField) where
  toFun := residueToUnramifiedHom hX m
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- The residue-to-unramified homomorphism as a profinite arrow. -/
noncomputable def residueToUnramifiedHomProfinite
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    profiniteGalGrp (maximalIdeal A).ResidueField
        (separableClosure (maximalIdeal A).ResidueField m.ResidueField) ⟶
      profiniteGalGrp (Spec (CommRingCat.of A)).functionField
        (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX) :=
  ProfiniteGrp.ofHom (residueToUnramifiedContinuousHom hX m)

/-- Applying the residue-to-unramified map is restriction of a residue lift. -/
theorem residueToUnramifiedHom_apply
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)]
    (σ : Gal(separableClosure (maximalIdeal A).ResidueField m.ResidueField/(maximalIdeal A).ResidueField)) :
    residueToUnramifiedHom hX m σ =
      restrictUnramifiedHom (Spec (CommRingCat.of A)).functionField
        (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)
        (Function.invFun
          (residueGaloisHom (Spec (CommRingCat.of A)).functionField m) σ).val := sorry

/-- The bottom arrow factors the residue action through restriction. -/
theorem residueToUnramifiedHom_comp
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    residueGaloisHomProfinite (Spec (CommRingCat.of A)).functionField m ≫
        residueToUnramifiedHomProfinite hX m =
      decompositionToGal (Spec (CommRingCat.of A)).functionField m ≫
        restrictUnramifiedHomProfinite (Spec (CommRingCat.of A)).functionField
          (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX) := sorry

/-- The profinite Galois inertia diagram associated with a normal local scheme. -/
noncomputable def galoisInertiaDiagram
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    InertiaDiagram
      (inertiaProfinite (Spec (CommRingCat.of A)).functionField m)
      (decompositionProfinite (Spec (CommRingCat.of A)).functionField m)
      (profiniteGalGrp (Spec (CommRingCat.of A)).functionField
        (SeparableClosure (Spec (CommRingCat.of A)).functionField))
      (profiniteGalGrp (maximalIdeal A).ResidueField
        (separableClosure (maximalIdeal A).ResidueField m.ResidueField))
      (profiniteGalGrp (Spec (CommRingCat.of A)).functionField
        (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)) :=
  InertiaDiagram.of _ _ _ _ _
    (inertiaToDecomposition (Spec (CommRingCat.of A)).functionField m)
    (decompositionToGal (Spec (CommRingCat.of A)).functionField m)
    (residueGaloisHomProfinite (Spec (CommRingCat.of A)).functionField m)
    (restrictUnramifiedHomProfinite (Spec (CommRingCat.of A)).functionField
      (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX))
    (residueToUnramifiedHomProfinite hX m)
    (inertiaToResidueTrivial (Spec (CommRingCat.of A)).functionField m)
    sorry sorry sorry

/-- The Galois inertia diagram satisfies its triangle, square, and trivial diagonal laws. -/
theorem galoisInertiaDiagram_spec
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    [IsIntegrallyClosed A]
    (hX : (Spec (CommRingCat.of A)).isNormal)
    (m : Ideal
      (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
    [m.IsMaximal] [m.LiesOver (maximalIdeal A)] :
    (galoisInertiaDiagram hX m).ushToUh ≫ (galoisInertiaDiagram hX m).uhToXh =
      (galoisInertiaDiagram hX m).ushToXh ∧
      CategoryTheory.CommSq
        (galoisInertiaDiagram hX m).uhToU
        (galoisInertiaDiagram hX m).uhToXh
        (galoisInertiaDiagram hX m).uToX
        (galoisInertiaDiagram hX m).xhToX ∧
        (∀ g : inertiaProfinite (Spec (CommRingCat.of A)).functionField m,
          (galoisInertiaDiagram hX m).ushToXh g = 1) := sorry

end EtaleFundamentalGroup
