/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.KernelPresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 46.5.5 (1): adequacy is equivalent to affine-open-cover kernel presentations. -/
@[stacks 06VK] #check (SheafOfModules.IsAdequate.iff_exists_affineOpenCover_kernelPresentation :
  ∀ {S : Scheme.{u}} {τ : StandardTopology}
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)),
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : S.AffineOpenCover, ∀ i : 𝒰.I₀,
        SheafOfModules.HasQuasicoherentKernelPresentation
          ((@RingedSite.Hom.modulePullback _ _
            (StandardTopology.Big.pullbackRingedHom τ (𝒰.f i))
            (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
              τ (𝒰.f i))).obj ℱ))

/- Lemma 46.5.5 (2): adequacy is equivalent to kernel presentations on a `τ`-cover. -/
@[stacks 06VK] #check (SheafOfModules.IsAdequate.iff_exists_cover_kernelPresentation :
  ∀ {S : Scheme.{u}} {τ : StandardTopology}
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)),
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : SemiRepresentableFamily.Over.{u} S,
        SemiRepresentableFamily.Over.IsCovering τ.precoverage 𝒰 ∧
          ∀ i : 𝒰.index,
            SheafOfModules.HasQuasicoherentKernelPresentation
              ((@RingedSite.Hom.modulePullback _ _
                (StandardTopology.Big.pullbackRingedHom τ (𝒰.obj i).hom)
                (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
                  τ (𝒰.obj i).hom)).obj ℱ))

/- Lemma 46.5.5 (3): adequacy is equivalent to adequacy after pullback on a `τ`-cover. -/
@[stacks 06VK] #check (SheafOfModules.IsAdequate.iff_exists_cover_pullback :
  ∀ {S : Scheme.{u}} {τ : StandardTopology}
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)),
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : SemiRepresentableFamily.Over.{u} S,
        SemiRepresentableFamily.Over.IsCovering τ.precoverage 𝒰 ∧
          ∀ i : 𝒰.index,
            SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
              SheafOfModules.affineEvaluationUnderlying
              ((@RingedSite.Hom.modulePullback _ _
                (StandardTopology.Big.pullbackRingedHom τ (𝒰.obj i).hom)
                (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
                  τ (𝒰.obj i).hom)).obj ℱ))

/- Lemma 46.5.5 (4): adequacy is equivalent to kernel presentations after pullback to every affine over `S`. -/
@[stacks 06VK] #check (SheafOfModules.IsAdequate.iff_forall_affine_kernelPresentation :
  ∀ {S : Scheme.{u}} {τ : StandardTopology}
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)),
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ ↔
      ∀ (U : Over S) [IsAffine U.left],
        SheafOfModules.HasQuasicoherentKernelPresentation
          ((@RingedSite.Hom.modulePullback _ _
            (StandardTopology.Big.pullbackRingedHom τ U.hom)
            (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
              τ U.hom)).obj ℱ))
