/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation criteria for formal smoothness

The presentation-independent criteria for a formally smooth algebra are exposed
at the `Algebra.Extension` and `Algebra.FormallySmooth.Criteria` layers.  The
two presentation properties are named predicates rather than repeated anonymous
existentials, so downstream statements can quantify over them directly.

@stack 031J
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.Extension

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- A presentation `P` has an infinitesimal section when `S →ₐ[R] P / ker(P → S)²`
splits the canonical quotient map. -/
@[stacks 031J "infinitesimal presentation section"]
def HasInfinitesimalSection (P : Extension.{w} R S) : Prop :=
  ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
    (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S

/-- A presentation `P` has a conormal retraction when its conormal map admits a
linear left inverse over `S`. -/
@[stacks 031J "conormal presentation retraction"]
def HasConormalRetraction (P : Extension.{w} R S) : Prop :=
  ∃ τ : P.CotangentSpace →ₗ[S] P.Cotangent,
    τ.comp P.cotangentComplex = LinearMap.id

end Algebra.Extension

namespace Algebra.FormallySmooth.Criteria

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

private theorem self_generators_toExtension_formallySmooth :
    Algebra.FormallySmooth R ((Algebra.Generators.self R S).toExtension).Ring := by
  change Algebra.FormallySmooth R (MvPolynomial S R)
  infer_instance

/-- Proposition 10.138.8 (Tag 031J): formal smoothness, presentation-level
infinitesimal sections, presentation-level conormal retractions, and the
projective/subsingleton cotangent criterion are all equivalent. -/
@[stacks 031J]
theorem tfae :
    List.TFAE
      [Algebra.FormallySmooth R S,
        ∃ P : Algebra.Extension.{max u v} R S,
          Algebra.FormallySmooth R P.Ring ∧ P.HasInfinitesimalSection,
        ∀ P : Algebra.Extension.{max u v} R S,
          Algebra.FormallySmooth R P.Ring → P.HasInfinitesimalSection,
        ∃ P : Algebra.Extension.{max u v} R S,
          Algebra.FormallySmooth R P.Ring ∧ P.HasConormalRetraction,
        ∀ P : Algebra.Extension.{max u v} R S,
          Algebra.FormallySmooth R P.Ring → P.HasConormalRetraction,
        Subsingleton (Algebra.H1Cotangent R S) ∧
          Module.Projective S Ω[S⁄R]] := by
  tfae_have 1 ↔ 6 := by
    simpa [and_comm] using (Algebra.formallySmooth_iff (R := R) (A := S))
  tfae_have 1 → 3 := by
    intro hS P hP
    letI : Algebra.FormallySmooth R P.Ring := hP
    change ∃ g, (IsScalarTower.toAlgHom R P.Ring S).kerSquareLift.comp g = AlgHom.id R S
    exact (Algebra.FormallySmooth.iff_split_surjection
      (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mp hS
  tfae_have 3 → 2 := by
    intro h
    let P : Algebra.Extension.{max u v} R S := (Algebra.Generators.self R S).toExtension
    have hP : Algebra.FormallySmooth R P.Ring := by
      simpa [P] using
        (self_generators_toExtension_formallySmooth (R := R) (S := S))
    exact ⟨P, hP, h P hP⟩
  tfae_have 2 → 4 := by
    rintro ⟨P, hP, hSection⟩
    letI : Algebra.FormallySmooth R P.Ring := hP
    have hS : Algebra.FormallySmooth R S :=
      (Algebra.FormallySmooth.iff_split_surjection
        (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr hSection
    exact ⟨P, hP,
      (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS⟩
  tfae_have 3 → 5 := by
    intro h P hP
    letI : Algebra.FormallySmooth R P.Ring := hP
    have hS : Algebra.FormallySmooth R S :=
      (Algebra.FormallySmooth.iff_split_surjection
        (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr (h P hP)
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS
  tfae_have 5 → 4 := by
    intro h
    let P : Algebra.Extension.{max u v} R S := (Algebra.Generators.self R S).toExtension
    have hP : Algebra.FormallySmooth R P.Ring := by
      simpa [P] using
        (self_generators_toExtension_formallySmooth (R := R) (S := S))
    exact ⟨P, hP, h P hP⟩
  tfae_have 4 → 1 := by
    rintro ⟨P, hP, hRetraction⟩
    letI : Algebra.FormallySmooth R P.Ring := hP
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mpr hRetraction
  tfae_finish

end Algebra.FormallySmooth.Criteria
