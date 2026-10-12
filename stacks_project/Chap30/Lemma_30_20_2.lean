/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.FiniteType
public import stacks_project.Chap30.Lemma_30_20_2_HigherDirectImage
public import stacks_project.Chap30.Lemma_30_20_2_Rees

/-!
# Lemma 30.20.2

For a proper morphism `f : X ⟶ Y` with `Y` locally Noetherian, a quasi-coherent
ideal sheaf `I ⊂ 𝒪_Y`, and a coherent `𝒪_X`-module `F`, the graded module sheaf
`M = ⨁_{n ≥ 0} R^p f_*(I^n F)` over the Rees algebra `A = ⨁_{n ≥ 0} I^n` is
quasi-coherent and of finite type.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open scoped BigOperators
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddCommGroup ι]
variable {𝒜 : GradedAlgebraSheaf 𝒪 ι}

/-- A fixed finite homogeneous family generates locally on an object if every homogeneous
section over an object above it has coefficient expressions after passing to a covering sieve.
The family is fixed independently of the degree, section, and covering sieve. -/
def LocallyHomogeneouslyGeneratesOn
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ index : Fin r, ℱ.sections (Opposite.op U) (degree index)) : Prop :=
  ∀ ⦃V : C⦄ (inclusion : V ⟶ U) (n : ι) (localSection : ℱ.sections (Opposite.op V) n),
    ∃ (cover : Sieve V), cover ∈ J V ∧
      ∀ ⦃W : C⦄ (restriction : W ⟶ V), cover restriction →
        ∃ (coefficientDegree : Fin r → ι)
          (degree_eq : ∀ index : Fin r, degree index + coefficientDegree index = n)
          (coefficient : ∀ index : Fin r,
            𝒜.sections (Opposite.op W) (coefficientDegree index)),
          (((ℱ n).val.map restriction.op).hom localSection) = ∑ index : Fin r,
            cast (congrArg (ℱ.sections (Opposite.op W)) (degree_eq index))
              (ℱ.smul (degree index) (coefficientDegree index) (Opposite.op W)
                (((ℱ (degree index)).val.map (restriction ≫ inclusion).op).hom
                  (generator index)) (coefficient index))

/-- The covering-local section criterion for a fixed finite homogeneous generating family. -/
theorem locallyHomogeneouslyGeneratesOn_iff
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ index : Fin r, ℱ.sections (Opposite.op U) (degree index)) :
    LocallyHomogeneouslyGeneratesOn ℱ U r degree generator ↔
      ∀ ⦃V : C⦄ (inclusion : V ⟶ U) (n : ι) (localSection : ℱ.sections (Opposite.op V) n),
        ∃ (cover : Sieve V), cover ∈ J V ∧
          ∀ ⦃W : C⦄ (restriction : W ⟶ V), cover restriction →
            ∃ (coefficientDegree : Fin r → ι)
              (degree_eq : ∀ index : Fin r, degree index + coefficientDegree index = n)
              (coefficient : ∀ index : Fin r,
                𝒜.sections (Opposite.op W) (coefficientDegree index)),
              (((ℱ n).val.map restriction.op).hom localSection) = ∑ index : Fin r,
                cast (congrArg (ℱ.sections (Opposite.op W)) (degree_eq index))
                  (ℱ.smul (degree index) (coefficientDegree index) (Opposite.op W)
                    (((ℱ (degree index)).val.map (restriction ≫ inclusion).op).hom
                      (generator index)) (coefficient index)) := sorry

/-- A graded module sheaf is locally of finite type if a cover carries finite homogeneous
families that generate locally, using one family for all degrees on each cover member. -/
def IsLocallyFiniteType (ℱ : GradedModuleSheaf 𝒜) : Prop :=
  ∃ (Index : Type u) (U : Index → C), J.CoversTop U ∧
    ∀ index : Index, ∃ (r : ℕ) (degree : Fin r → ι)
      (generator : ∀ generatorIndex : Fin r,
        ℱ.sections (Opposite.op (U index)) (degree generatorIndex)),
      LocallyHomogeneouslyGeneratesOn ℱ (U index) r degree generator

/-- Local finite type is finite homogeneous generation on a cover, with expressions local
on each member rather than required on entire subobjects. -/
theorem isLocallyFiniteType_iff (ℱ : GradedModuleSheaf 𝒜) :
    IsLocallyFiniteType ℱ ↔
      ∃ (Index : Type u) (U : Index → C), J.CoversTop U ∧
        ∀ index : Index, ∃ (r : ℕ) (degree : Fin r → ι)
          (generator : ∀ generatorIndex : Fin r,
            ℱ.sections (Opposite.op (U index)) (degree generatorIndex)),
          LocallyHomogeneouslyGeneratesOn ℱ (U index) r degree generator := sorry

end SheafOfModules.RingedSite.GradedModuleSheaf

namespace AlgebraicGeometry.Scheme.Hom
namespace IdealPowerCohomology

variable {Y : Scheme.{u}} (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
variable {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)

/-- Lemma 30.20.2 (1): given a morphism of schemes `f : X ⟶ Y`, a quasi-coherent
sheaf `F` on `X`, and a quasi-coherent sheaf of ideals `I ⊂ 𝒪_Y`, if `Y` is
locally Noetherian, `f` is proper, and `F` is coherent, then
`M = ⨁_{n ≥ 0} R^p f_*(I^n F)` is a quasi-coherent graded module over
`A = ⨁_{n ≥ 0} I^n`. -/
@[stacks 02O9]
instance isQuasicoherent [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent]
    (n : ℤ) : (gradedModule I f F p n).IsQuasicoherent :=
  sorry

/-- Lemma 30.20.2 (2): under the same hypotheses, `M = ⨁_{n ≥ 0} R^p f_*(I^n F)`
is locally of finite type as a graded module over `A = ⨁_{n ≥ 0} I^n`, with one finite
homogeneous generating family per neighborhood, uniform across all degrees. -/
@[stacks 02O9]
theorem isFiniteType [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] :
    GradedModuleSheaf.IsLocallyFiniteType.{u, u} (gradedModule I f F p) :=
  sorry

end IdealPowerCohomology
end AlgebraicGeometry.Scheme.Hom
