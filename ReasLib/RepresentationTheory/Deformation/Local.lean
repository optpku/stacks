/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod
public import ReasLib.RepresentationTheory.Matrix

@[expose] public section

noncomputable section

universe u v w

open Matrix Matrix.GeneralLinearGroup IsLocalRing

namespace Deformation

/-- The canonical `ℤ_[ℓ]`-algebra structure on `ZMod ℓ` via `PadicInt.toZMod`. -/
instance instAlgebraZMod (ℓ : ℕ) [Fact ℓ.Prime] : Algebra ℤ_[ℓ] (ZMod ℓ) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- A commutative local `ℤ_[ℓ]`-algebra is `ℓ`-adic when its structure map is local and identifies residue fields with `ZMod ℓ`. -/
class IsLAdicAlgebra (ℓ : ℕ) [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] : Prop where
  /-- The structure map `ℤ_[ℓ] →+* R` is a local homomorphism. -/
  isLocalHom : IsLocalHom (algebraMap ℤ_[ℓ] R)
  /-- The induced map of residue fields is bijective. -/
  residueBijective :
    Function.Bijective
      (@ResidueField.map ℤ_[ℓ] R _ _ _ _ (algebraMap ℤ_[ℓ] R) isLocalHom)

/-- The structure map of an `ℓ`-adic algebra is a local homomorphism. -/
instance instIsLocalHomAlgebraMap {ℓ : ℕ} [Fact ℓ.Prime] {R : Type u}
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    IsLocalHom (algebraMap ℤ_[ℓ] R) :=
  IsLAdicAlgebra.isLocalHom

/-- `ZMod ℓ` is an `ℓ`-adic algebra over `ℤ_[ℓ]`. -/
instance instZMod (ℓ : ℕ) [Fact ℓ.Prime] : IsLAdicAlgebra ℓ (ZMod ℓ) := by
  refine ⟨inferInstance, ?_⟩
  refine ⟨(ResidueField.map _).injective, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := residue_surjective (R := ZMod ℓ) y
  obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (algebraMap ℤ_[ℓ] (ZMod ℓ)) z
  exact ⟨residue ℤ_[ℓ] x, rfl⟩

/-- The `ℓ`-adic integers are an `ℓ`-adic algebra over themselves. -/
instance instPadicInt (ℓ : ℕ) [Fact ℓ.Prime] : IsLAdicAlgebra ℓ ℤ_[ℓ] := by
  refine ⟨inferInstance, ?_⟩
  simpa only [Algebra.algebraMap_self, ResidueField.map_id, RingHom.coe_id] using
    (Function.bijective_id : Function.Bijective (id : ResidueField ℤ_[ℓ] → _))

/-- An `ℓ`-adic algebra has a local structure map and a bijective residue-field map. -/
theorem IsLAdicAlgebra.spec {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    IsLocalHom (algebraMap ℤ_[ℓ] R) ∧
      Function.Bijective (ResidueField.map (algebraMap ℤ_[ℓ] R)) :=
  ⟨IsLAdicAlgebra.isLocalHom, IsLAdicAlgebra.residueBijective⟩

/-- The `ℓ`-adic algebra condition is equivalent to locality and residue-field bijectivity. -/
theorem isLAdicAlgebra_iff {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] :
    IsLAdicAlgebra ℓ R ↔
      ∃ h : IsLocalHom (algebraMap ℤ_[ℓ] R),
        Function.Bijective (@ResidueField.map ℤ_[ℓ] R _ _ _ _ (algebraMap ℤ_[ℓ] R) h) := by
  constructor
  · intro h
    exact ⟨h.isLocalHom, h.residueBijective⟩
  · rintro ⟨h, hb⟩
    exact ⟨h, hb⟩

/-- The structure map `ℤ_[ℓ] →+* ZMod ℓ` is `PadicInt.toZMod`. -/
theorem algebraMap_zmod (ℓ : ℕ) [Fact ℓ.Prime] :
    algebraMap ℤ_[ℓ] (ZMod ℓ) = PadicInt.toZMod := rfl

/-- The residue field of an `ℓ`-adic algebra is canonically identified with `ZMod ℓ`. -/
def residueFieldEquiv {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    ResidueField R ≃+* ZMod ℓ :=
  (RingEquiv.ofBijective (ResidueField.map (algebraMap ℤ_[ℓ] R))
      IsLAdicAlgebra.residueBijective).symm.trans PadicInt.residueField

/-- The residue field identification sends the structure map to the canonical one. -/
theorem residueFieldEquiv_map {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R]
    (x : ResidueField ℤ_[ℓ]) :
    residueFieldEquiv R (ResidueField.map (algebraMap ℤ_[ℓ] R) x) =
      PadicInt.residueField x := by
  exact congrArg PadicInt.residueField
    ((RingEquiv.ofBijective (ResidueField.map (algebraMap ℤ_[ℓ] R))
      IsLAdicAlgebra.residueBijective).symm_apply_apply x)

/-- The residue homomorphism from an `ℓ`-adic algebra to `ZMod ℓ`. -/
def residueHom {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    R →+* ZMod ℓ :=
  (residueFieldEquiv R).toRingHom.comp (residue R)

/-- The residue homomorphism factors through the residue field equivalence. -/
theorem residueHom_eq {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    (residueHom R : R →+* ZMod ℓ) =
      (residueFieldEquiv R).toRingHom.comp (residue R) := rfl

/-- Reduction of `GL n R` along the residue homomorphism of an `ℓ`-adic algebra. -/
def residueGL {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [IsLAdicAlgebra ℓ R] : GL n R →* GL n (ZMod ℓ) :=
  GeneralLinearGroup.map (residueHom R)

/-- The residue map on `GL n` is `GL.map` of `residueHom`. -/
theorem residueGL_eq {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [IsLAdicAlgebra ℓ R] :
    (residueGL : GL n R →* GL n (ZMod ℓ)) = GeneralLinearGroup.map (residueHom R) := rfl

/-- On `ℤ_[ℓ]`, residue reduction of `GL n` is `GL.map PadicInt.toZMod`. -/
theorem residueGL_padicInt {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v}
    [DecidableEq n] [Fintype n] :
    (residueGL : GL n ℤ_[ℓ] →* GL n (ZMod ℓ)) = GeneralLinearGroup.map PadicInt.toZMod := by
  rw [residueGL_eq]
  congr 1
  ext x
  change residueFieldEquiv ℤ_[ℓ] (residue ℤ_[ℓ] x) = PadicInt.toZMod x
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  change residueFieldEquiv ℤ_[ℓ] (residue ℤ_[ℓ] x) = PadicInt.residueField (residue ℤ_[ℓ] x)
  simpa only [Algebra.algebraMap_self, ResidueField.map_id, RingHom.id_apply] using
    residueFieldEquiv_map ℤ_[ℓ] (residue ℤ_[ℓ] x)

/-- Residue reduction of `GL n` is compatible with local `ℤ_[ℓ]`-algebra maps. -/
theorem residueGL_comp {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R S : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra ℤ_[ℓ] R] [Algebra ℤ_[ℓ] S]
    [IsLAdicAlgebra ℓ R] [IsLAdicAlgebra ℓ S]
    (ψ : R →ₐ[ℤ_[ℓ]] S) [IsLocalHom ψ.toRingHom] :
    (residueGL : GL n S →* GL n (ZMod ℓ)).comp (GeneralLinearGroup.map ψ.toRingHom) =
      (residueGL : GL n R →* GL n (ZMod ℓ)) := by
  rw [residueGL_eq, residueGL_eq, ← GeneralLinearGroup.map_comp]
  congr 1
  ext r
  change residueFieldEquiv S (residue S (ψ.toRingHom r)) = residueFieldEquiv R (residue R r)
  obtain ⟨x, hx⟩ := (IsLAdicAlgebra.residueBijective (ℓ := ℓ) (R := R)).2 (residue R r)
  have hcomm : ResidueField.map ψ.toRingHom
      (ResidueField.map (algebraMap ℤ_[ℓ] R) x) =
      ResidueField.map (algebraMap ℤ_[ℓ] S) x := by
    obtain ⟨a, rfl⟩ := residue_surjective (R := ℤ_[ℓ]) x
    simp only [ResidueField.map_residue]
    change residue S (ψ (algebraMap ℤ_[ℓ] R a)) = residue S (algebraMap ℤ_[ℓ] S a)
    rw [ψ.commutes]
  rw [← ResidueField.map_residue ψ.toRingHom, ← hx, hcomm]
  rw [residueFieldEquiv_map, residueFieldEquiv_map]

/-- A continuous `GL n R`-valued lift of a residual representation, up to conjugacy after reduction. -/
def IsDeformation {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρ : G →ₜ* GL n R) : Prop :=
  IsConjugate (residueGL.comp ρ.toMonoidHom) ρ₀.toMonoidHom

/-- The deformation predicate is conjugacy of the residual reduction with `ρ₀`. -/
theorem isDeformation_iff {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρ : G →ₜ* GL n R) :
    IsDeformation ρ₀ ρ ↔
      IsConjugate (residueGL.comp ρ.toMonoidHom) ρ₀.toMonoidHom := Iff.rfl

/-- A complete local lift is universal when every complete local deformation factors uniquely through it up to conjugacy. -/
def IsUniversalDeformation {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρuniv : G →ₜ* GL n R) : Prop :=
  IsDeformation ρ₀ ρuniv ∧
    ∀ (S : Type u) [CommRing S] [IsLocalRing S] [Algebra ℤ_[ℓ] S]
      [TopologicalSpace S] [IsTopologicalRing S]
      [Fact (IsAdic (maximalIdeal S))]
      [IsAdicComplete (maximalIdeal S) S] [IsLAdicAlgebra ℓ S]
      (σ : G →ₜ* GL n S),
      IsDeformation ρ₀ σ →
        ∃! ψ : R →ₐ[ℤ_[ℓ]] S,
          IsLocalHom ψ.toRingHom ∧
            IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom) σ.toMonoidHom

/-- The universal deformation property is a deformation together with unique local factorization of every complete local lift. -/
theorem isUniversalDeformation_iff {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w}
    {R : Type u} [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρuniv : G →ₜ* GL n R) :
    IsUniversalDeformation ρ₀ ρuniv ↔
      IsDeformation ρ₀ ρuniv ∧
        ∀ (S : Type u) [CommRing S] [IsLocalRing S] [Algebra ℤ_[ℓ] S]
          [TopologicalSpace S] [IsTopologicalRing S]
          [Fact (IsAdic (maximalIdeal S))]
          [IsAdicComplete (maximalIdeal S) S] [IsLAdicAlgebra ℓ S]
          (σ : G →ₜ* GL n S),
          IsDeformation ρ₀ σ →
            ∃! ψ : R →ₐ[ℤ_[ℓ]] S,
              IsLocalHom ψ.toRingHom ∧
                IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom) σ.toMonoidHom := Iff.rfl

/-- A universal deformation uniquely receives every complete local lift along a local algebra map, up to conjugacy. -/
theorem existsUnique_lift {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    {ρ₀ : G →ₜ* GL n (ZMod ℓ)} {ρuniv : G →ₜ* GL n R}
    (huniv : IsUniversalDeformation ρ₀ ρuniv)
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra ℤ_[ℓ] S]
    [TopologicalSpace S] [IsTopologicalRing S]
    [Fact (IsAdic (maximalIdeal S))]
    [IsAdicComplete (maximalIdeal S) S] [IsLAdicAlgebra ℓ S]
    (σ : G →ₜ* GL n S) (hσ : IsDeformation ρ₀ σ) :
    ∃! ψ : R →ₐ[ℤ_[ℓ]] S,
      IsLocalHom ψ.toRingHom ∧
        IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom) σ.toMonoidHom :=
  huniv.2 S σ hσ

end Deformation
