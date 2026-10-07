module

public import stacks_project.Chap27.Lemma_27_11_8_Veronese
public import stacks_project.Chap27.Lemma_27_8_7_AssociatedSheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open AlgebraicGeometry.Proj.AssociatedModule
open GradedModule.TensorProduct

universe u

namespace AlgebraicGeometry.Proj.Veronese

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (d : ℕ)

/-- Coherent comparison data between `Proj(𝒜)` and the projective spectrum of its `d`th
Veronese ring, including associated-sheaf and monoidal compatibility. -/
structure Comparison where
  /-- The scheme-level Veronese comparison. -/
  schemeIso :
    AlgebraicGeometry.Proj 𝒜 ≅
      AlgebraicGeometry.Proj (GradedRing.Veronese.grading 𝒜 d)
  /-- The comparison of associated sheaves for every genuine graded module. -/
  associatedIso :
    ∀ {M τ : Type u} [AddCommGroup M] [Module A M] [SetLike τ M]
      [AddSubgroupClass τ M] (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul 𝒜 ℳ],
      AlgebraicGeometry.Proj.associatedSheaf 𝒜 ℳ ≅
        (Scheme.Modules.pullback schemeIso.hom).obj
          (AlgebraicGeometry.Proj.associatedSheaf
            (GradedRing.Veronese.grading 𝒜 d)
            (GradedModule.Veronese.grading ℳ d))
  /-- The tensor grading of the two Veronese modules is identified with the Veronese of the
  original tensor grading after applying the associated-sheaf construction. -/
  tensorIso :
    ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
      (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
      [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
      [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ],
      AlgebraicGeometry.Proj.associatedSheaf
          (GradedRing.Veronese.grading 𝒜 d)
          (grading (GradedRing.Veronese 𝒜 d)
            (GradedModule.Veronese.grading ℳ d)
            (GradedModule.Veronese.grading ℵ d)) ≅
        AlgebraicGeometry.Proj.associatedSheaf
          (GradedRing.Veronese.grading 𝒜 d)
          (GradedModule.Veronese.grading
            (grading A ℳ ℵ) d)
  /-- On a homogeneous element of degree `n * d`, the scheme comparison identifies the
  corresponding standard opens. -/
  mapBasicOpen :
    ∀ (n : ℕ) (f : 𝒜 (n * d)),
      schemeIso.hom ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen
            (GradedRing.Veronese.grading 𝒜 d)
            (DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n f) =
        AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)
  /-- The associated-sheaf comparisons commute with the canonical tensor multiplication map and
  the inverse of the pullback tensorator. -/
  tensorNaturality :
    ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
      (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
      [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
      [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ],
      ((associatedIso ℳ).hom ⊗ₘ (associatedIso ℵ).hom) ≫
            (Scheme.Modules.pullbackTensorIso schemeIso.hom
              (AlgebraicGeometry.Proj.associatedSheaf
                (GradedRing.Veronese.grading 𝒜 d)
                (GradedModule.Veronese.grading ℳ d))
              (AlgebraicGeometry.Proj.associatedSheaf
                (GradedRing.Veronese.grading 𝒜 d)
                (GradedModule.Veronese.grading ℵ d))).inv ≫
          (Scheme.Modules.pullback schemeIso.hom).map
            (Tensor.hom
                (GradedRing.Veronese.grading 𝒜 d)
                (GradedModule.Veronese.grading ℳ d)
                (GradedModule.Veronese.grading ℵ d) ≫
              (tensorIso ℳ ℵ).hom) =
        Tensor.hom 𝒜 ℳ ℵ ≫
          (associatedIso (gradingFor A 𝒜 ℳ ℵ)).hom

/-- Construct a `Comparison` from its three concrete isomorphism families and two coherence
properties. -/
def Comparison.of
    (schemeIso :
      AlgebraicGeometry.Proj 𝒜 ≅
        AlgebraicGeometry.Proj (GradedRing.Veronese.grading 𝒜 d))
    (associatedIso :
      ∀ {M τ : Type u} [AddCommGroup M] [Module A M] [SetLike τ M]
        [AddSubgroupClass τ M] (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
        [SetLike.GradedSMul 𝒜 ℳ],
        AlgebraicGeometry.Proj.associatedSheaf 𝒜 ℳ ≅
          (Scheme.Modules.pullback schemeIso.hom).obj
            (AlgebraicGeometry.Proj.associatedSheaf
              (GradedRing.Veronese.grading 𝒜 d)
              (GradedModule.Veronese.grading ℳ d)))
    (tensorIso :
      ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
        (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
        [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
        [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ],
        AlgebraicGeometry.Proj.associatedSheaf
            (GradedRing.Veronese.grading 𝒜 d)
            (grading (GradedRing.Veronese 𝒜 d)
              (GradedModule.Veronese.grading ℳ d)
              (GradedModule.Veronese.grading ℵ d)) ≅
          AlgebraicGeometry.Proj.associatedSheaf
            (GradedRing.Veronese.grading 𝒜 d)
            (GradedModule.Veronese.grading
              (grading A ℳ ℵ) d))
    (mapBasicOpen :
      ∀ (n : ℕ) (f : 𝒜 (n * d)),
        schemeIso.hom ⁻¹ᵁ
            AlgebraicGeometry.Proj.basicOpen
              (GradedRing.Veronese.grading 𝒜 d)
              (DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n f) =
          AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (tensorNaturality :
      ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
        (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
        [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
        [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ],
        ((associatedIso ℳ).hom ⊗ₘ (associatedIso ℵ).hom) ≫
              (Scheme.Modules.pullbackTensorIso schemeIso.hom
                (AlgebraicGeometry.Proj.associatedSheaf
                  (GradedRing.Veronese.grading 𝒜 d)
                  (GradedModule.Veronese.grading ℳ d))
                (AlgebraicGeometry.Proj.associatedSheaf
                  (GradedRing.Veronese.grading 𝒜 d)
                  (GradedModule.Veronese.grading ℵ d))).inv ≫
            (Scheme.Modules.pullback schemeIso.hom).map
              (Tensor.hom
                  (GradedRing.Veronese.grading 𝒜 d)
                  (GradedModule.Veronese.grading ℳ d)
                  (GradedModule.Veronese.grading ℵ d) ≫
                (tensorIso ℳ ℵ).hom) =
          Tensor.hom 𝒜 ℳ ℵ ≫
            (associatedIso (gradingFor A 𝒜 ℳ ℵ)).hom) :
    Comparison 𝒜 d where
  schemeIso := schemeIso
  associatedIso := associatedIso
  tensorIso := tensorIso
  mapBasicOpen := mapBasicOpen
  tensorNaturality := tensorNaturality

/-- The lower multiplication arrow in the Veronese comparison square. -/
noncomputable def Comparison.tensorMap (c : Comparison 𝒜 d)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
    [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ] :=
  Tensor.hom
      (GradedRing.Veronese.grading 𝒜 d)
      (GradedModule.Veronese.grading ℳ d)
      (GradedModule.Veronese.grading ℵ d) ≫
    (c.tensorIso ℳ ℵ).hom

/-- The Veronese tensor map is the canonical associated tensor map followed by the stored
tensor-grading comparison. -/
theorem Comparison.tensorMap_def (c : Comparison 𝒜 d)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
    [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ] :
    Comparison.tensorMap 𝒜 d c ℳ ℵ =
      Tensor.hom
          (GradedRing.Veronese.grading 𝒜 d)
          (GradedModule.Veronese.grading ℳ d)
          (GradedModule.Veronese.grading ℵ d) ≫
        (c.tensorIso ℳ ℵ).hom := sorry

/-- The standard-open characterization and tensor naturality properties stored by a Veronese
comparison. -/
theorem Comparison.spec (c : Comparison 𝒜 d) :
    (∀ (n : ℕ) (f : 𝒜 (n * d)),
      c.schemeIso.hom ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen
            (GradedRing.Veronese.grading 𝒜 d)
            (DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n f) =
        AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) ∧
    (∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
      (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
      [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
      [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ],
      ((c.associatedIso ℳ).hom ⊗ₘ (c.associatedIso ℵ).hom) ≫
            (Scheme.Modules.pullbackTensorIso c.schemeIso.hom
              (AlgebraicGeometry.Proj.associatedSheaf
                (GradedRing.Veronese.grading 𝒜 d)
                (GradedModule.Veronese.grading ℳ d))
              (AlgebraicGeometry.Proj.associatedSheaf
                (GradedRing.Veronese.grading 𝒜 d)
                (GradedModule.Veronese.grading ℵ d))).inv ≫
          (Scheme.Modules.pullback c.schemeIso.hom).map
            (Comparison.tensorMap 𝒜 d c ℳ ℵ) =
        Tensor.hom 𝒜 ℳ ℵ ≫
          (c.associatedIso (gradingFor A 𝒜 ℳ ℵ)).hom) := sorry

/-- Lemma 27.11.8: for `1 ≤ d`, the projective spectrum of a graded ring admits a coherent
Veronese comparison whose scheme isomorphism has the canonical standard-open behavior and whose
associated-sheaf isomorphism is available for every genuine graded module.  Applied to shifted
regular modules, the latter gives the twist comparisons; its tensor specialization is the
compatibility with the multiplication maps. -/
@[stacks 0B5J]
theorem existsComparison (hd : 1 ≤ d) : Nonempty (Comparison 𝒜 d) := sorry

end AlgebraicGeometry.Proj.Veronese
