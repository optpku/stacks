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
public import stacks_project.Chap64.Theorem_64_31_10_GLRep

/-!
# Mazur ℓ-adic algebras and universal deformations of residual GLₙ representations

This leaf owns complete local `ℤ_[ℓ]`-algebras with residue field `ZMod ℓ`, the
canonical residue map on `GL n`, and the universal-property predicate for a
deformation of a residual representation.
-/

@[expose] public section

noncomputable section

universe u v w

open Matrix Matrix.GeneralLinearGroup IsLocalRing

namespace Deformation

/-- The canonical `ℤ_[ℓ]`-algebra structure on `ZMod ℓ` via `PadicInt.toZMod`. -/
instance instAlgebraZMod (ℓ : ℕ) [Fact ℓ.Prime] : Algebra ℤ_[ℓ] (ZMod ℓ) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- A commutative local `ℤ_[ℓ]`-algebra is `ℓ`-adic when the structure map is local and
induces a bijection on residue fields, so the residue field is identified with `ZMod ℓ`.
Completeness is recorded separately by `IsAdicComplete`. -/
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
instance instZMod (ℓ : ℕ) [Fact ℓ.Prime] : IsLAdicAlgebra ℓ (ZMod ℓ) := sorry

/-- The `ℓ`-adic integers are an `ℓ`-adic algebra over themselves. -/
instance instPadicInt (ℓ : ℕ) [Fact ℓ.Prime] : IsLAdicAlgebra ℓ ℤ_[ℓ] := sorry

/-- An `ℓ`-adic algebra is a local `ℤ_[ℓ]`-algebra whose residue field identifies with `ZMod ℓ`. -/
theorem IsLAdicAlgebra.spec {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    IsLocalHom (algebraMap ℤ_[ℓ] R) ∧
      Function.Bijective (ResidueField.map (algebraMap ℤ_[ℓ] R)) := sorry

/-- Unfolding of the `ℓ`-adic algebra condition into a local structure map together with
a residue-field bijection. -/
theorem isLAdicAlgebra_iff {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] :
    IsLAdicAlgebra ℓ R ↔
      ∃ h : IsLocalHom (algebraMap ℤ_[ℓ] R),
        Function.Bijective (@ResidueField.map ℤ_[ℓ] R _ _ _ _ (algebraMap ℤ_[ℓ] R) h) := sorry

/-- The structure map `ℤ_[ℓ] →+* ZMod ℓ` is `PadicInt.toZMod`. -/
theorem algebraMap_zmod (ℓ : ℕ) [Fact ℓ.Prime] :
    algebraMap ℤ_[ℓ] (ZMod ℓ) = PadicInt.toZMod := sorry

/-- The canonical identification of the residue field of an `ℓ`-adic algebra with `ZMod ℓ`. -/
def residueFieldEquiv {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    ResidueField R ≃+* ZMod ℓ :=
  (RingEquiv.ofBijective (ResidueField.map (algebraMap ℤ_[ℓ] R))
      IsLAdicAlgebra.residueBijective).symm.trans PadicInt.residueField

/-- The residue homomorphism `R →+* ZMod ℓ` of an `ℓ`-adic algebra. -/
def residueHom {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    R →+* ZMod ℓ :=
  (residueFieldEquiv R).toRingHom.comp (residue R)

/-- The residue homomorphism factors as residue modulo the maximal ideal, followed by
the canonical identification of residue fields with `ZMod ℓ`. -/
theorem residueHom_eq {ℓ : ℕ} [Fact ℓ.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLAdicAlgebra ℓ R] :
    (residueHom R : R →+* ZMod ℓ) =
      (residueFieldEquiv R).toRingHom.comp (residue R) := sorry

/-- Reduction of `GL n R` along the residue homomorphism of an `ℓ`-adic algebra. -/
def residueGL {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [IsLAdicAlgebra ℓ R] : GL n R →* GL n (ZMod ℓ) :=
  GeneralLinearGroup.map (residueHom R)

/-- The residue map on `GL n` is `GL.map` of `residueHom`. -/
theorem residueGL_eq {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [IsLAdicAlgebra ℓ R] :
    (residueGL : GL n R →* GL n (ZMod ℓ)) = GeneralLinearGroup.map (residueHom R) := sorry

/-- On `ℤ_[ℓ]`, residue reduction of `GL n` is `GL.map PadicInt.toZMod`. -/
theorem residueGL_padicInt {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v}
    [DecidableEq n] [Fintype n] :
    (residueGL : GL n ℤ_[ℓ] →* GL n (ZMod ℓ)) = GeneralLinearGroup.map PadicInt.toZMod := sorry

/-- Residue reduction of `GL n` is compatible with local `ℤ_[ℓ]`-algebra maps. -/
theorem residueGL_comp {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {R S : Type u}
    [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra ℤ_[ℓ] R] [Algebra ℤ_[ℓ] S]
    [IsLAdicAlgebra ℓ R] [IsLAdicAlgebra ℓ S]
    (ψ : R →ₐ[ℤ_[ℓ]] S) [IsLocalHom ψ.toRingHom] :
    (residueGL : GL n S →* GL n (ZMod ℓ)).comp (GeneralLinearGroup.map ψ.toRingHom) =
      (residueGL : GL n R →* GL n (ZMod ℓ)) := sorry

/-- A continuous `GL n R`-valued lift of a residual representation, up to conjugacy on
residue reduction. -/
def IsDeformation {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρ : G →ₜ* GL n R) : Prop :=
  IsConjugate (residueGL.comp ρ.toMonoidHom) ρ₀.toMonoidHom

/-- Unfolding of the deformation predicate as conjugacy of the residual reduction with `ρ₀`. -/
theorem isDeformation_iff {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (ρ : G →ₜ* GL n R) :
    IsDeformation ρ₀ ρ ↔
      IsConjugate (residueGL.comp ρ.toMonoidHom) ρ₀.toMonoidHom := sorry

/-- A continuous lift `ρuniv` over a complete local `ℓ`-adic algebra `R` is a universal
deformation of `ρ₀` when every complete local lift factors uniquely through a local
`ℤ_[ℓ]`-algebra map, up to conjugacy. -/
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

/-- Unfolding of the universal deformation property into a deformation together with
unique local factoring of every complete local lift, up to conjugacy. -/
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
                IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom) σ.toMonoidHom := sorry

/-- A universal deformation uniquely receives every complete local lift along a local
`ℤ_[ℓ]`-algebra map, up to conjugacy. -/
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
        IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom) σ.toMonoidHom := sorry

end Deformation
