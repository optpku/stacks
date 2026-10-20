module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor.Comparison
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe uA uσ

namespace AlgebraicGeometry

open Proj.AssociatedModule
open GradedModule.TensorProduct

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M N : Type uA} [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]
variable [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]

/- Lemma 27.9.1 (1): the canonical morphism from the tensor product of two associated
graded-module sheaves on `Proj 𝒜` to the sheaf associated to their graded tensor product. -/
@[stacks 01MK] #check
  (Tensor.hom 𝒜 ℳ ℵ :
    (tensorObj (Proj.AssociatedModule.sheaf 𝒜 ℳ)
      (Proj.AssociatedModule.sheaf 𝒜 ℵ) : (Proj 𝒜).Modules) ⟶
        Proj.AssociatedModule.sheaf 𝒜 (grading A ℳ ℵ))

variable {d : ℕ} (f : 𝒜 d) (hd : 0 < d)

/- Lemma 27.9.1 (2): on every positive standard open, the canonical sheaf morphism agrees with
the tensor comparison on degree-zero homogeneous localizations. -/
@[stacks 01MK] #check
  (Tensor.away 𝒜 ℳ ℵ f hd :
    CommSq (Tensor.awayHom 𝒜 ℳ ℵ f) (Tensor.awaySectionHom 𝒜 ℳ ℵ f hd)
      (Proj.AssociatedModule.awaySectionHom 𝒜 (grading A ℳ ℵ) f hd)
      ((ModuleCat.restrictScalars
        (Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).map
          ((Tensor.hom 𝒜 ℳ ℵ).val.app (op (Proj.basicOpen 𝒜 (f : A))))))

variable (x : Proj 𝒜)

/- Lemma 27.9.1 (3): on every stalk, the canonical sheaf morphism agrees with the tensor
comparison at the corresponding homogeneous prime. -/
@[stacks 01MK] #check
  (Tensor.stalk 𝒜 ℳ ℵ x :
    CommSq
      (RingedSpace.moduleStalkHom x (Tensor.hom 𝒜 ℳ ℵ))
      ((RingedSpace.Tensor.Stalk.comparisonIso
          (Proj.AssociatedModule.sheaf 𝒜 ℳ)
          (Proj.AssociatedModule.sheaf 𝒜 ℵ) x).hom ≫
        (Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x ⊗ₘ
          Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℵ x))
      (Proj.AssociatedModule.stalkToPointLinearMap 𝒜 (grading A ℳ ℵ) x)
      (Tensor.stalkHom 𝒜 ℳ ℵ x))

/- Lemma 27.9.1 (4): the degree-zero global-section square for the canonical tensor morphism
commutes. -/
@[stacks 01MK] #check
  (Tensor.globalSections 𝒜 ℳ ℵ :
    CommSq (Tensor.degreeZeroHom 𝒜 ℳ ℵ) (Tensor.degreeZeroSectionHom 𝒜 ℳ ℵ)
      (Proj.AssociatedModule.degreeZeroToGlobalSectionsHom 𝒜
        (grading A ℳ ℵ))
      ((ModuleCat.restrictScalars
        (Proj.AssociatedModule.degreeZeroRingHom 𝒜)).map
          ((Tensor.hom 𝒜 ℳ ℵ).val.app (op ⊤))))

end AlgebraicGeometry
