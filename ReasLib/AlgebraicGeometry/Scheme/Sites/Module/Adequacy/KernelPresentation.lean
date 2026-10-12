/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S T : Scheme.{u}} {τ : StandardTopology}

/-- A module sheaf on the big standard site has a quasicoherent kernel presentation if it is
isomorphic to the kernel of the associated-module image of a morphism in `Scheme.QCoh`. -/
def HasQuasicoherentKernelPresentation
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ T)) : Prop :=
  ∃ (G H : Scheme.QCoh T) (φ : G ⟶ H),
    Nonempty
      (ℱ ≅ kernel ((Scheme.AssociatedModule.bigModuleFunctor T τ).map φ))

/-- A quasicoherent kernel presentation is exactly the displayed choice of two quasicoherent
modules, a morphism between them, and an isomorphism to its associated-module kernel. -/
theorem hasQuasicoherentKernelPresentation_iff
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ T)) :
    HasQuasicoherentKernelPresentation ℱ ↔
      ∃ (G H : Scheme.QCoh T) (φ : G ⟶ H),
        Nonempty
          (ℱ ≅ kernel ((Scheme.AssociatedModule.bigModuleFunctor T τ).map φ)) := sorry

/-- Quasicoherent kernel presentations transport across isomorphisms of module sheaves. -/
theorem HasQuasicoherentKernelPresentation.of_iso
    {ℱ ℱ' : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ T)}
    (hℱ : HasQuasicoherentKernelPresentation ℱ) (e : ℱ ≅ ℱ') :
    HasQuasicoherentKernelPresentation ℱ' := sorry

namespace IsAdequate

variable (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))

/-- Adequacy is equivalent to admitting quasicoherent kernel presentations after restriction to
the members of an affine open cover. -/
theorem iff_exists_affineOpenCover_kernelPresentation :
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : S.AffineOpenCover, ∀ i : 𝒰.I₀,
        HasQuasicoherentKernelPresentation
          ((@RingedSite.Hom.modulePullback _ _
            (StandardTopology.Big.pullbackRingedHom τ (𝒰.f i))
            (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
              τ (𝒰.f i))).obj ℱ) := sorry

/-- Adequacy is equivalent to admitting quasicoherent kernel presentations after pullback along
every member of some `τ`-cover. -/
theorem iff_exists_cover_kernelPresentation :
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : SemiRepresentableFamily.Over.{u} S,
        SemiRepresentableFamily.Over.IsCovering τ.precoverage 𝒰 ∧
          ∀ i : 𝒰.index,
            HasQuasicoherentKernelPresentation
              ((@RingedSite.Hom.modulePullback _ _
                (StandardTopology.Big.pullbackRingedHom τ (𝒰.obj i).hom)
                (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
                  τ (𝒰.obj i).hom)).obj ℱ) := sorry

/-- Adequacy is equivalent to becoming adequate after pullback along every member of some
`τ`-cover. -/
theorem iff_exists_cover_pullback :
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ ↔
      ∃ 𝒰 : SemiRepresentableFamily.Over.{u} S,
        SemiRepresentableFamily.Over.IsCovering τ.precoverage 𝒰 ∧
          ∀ i : 𝒰.index,
            SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
              affineEvaluationUnderlying
              ((@RingedSite.Hom.modulePullback _ _
                (StandardTopology.Big.pullbackRingedHom τ (𝒰.obj i).hom)
                (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
                  τ (𝒰.obj i).hom)).obj ℱ) := sorry

/-- Adequacy is equivalent to admitting a quasicoherent kernel presentation after pullback to
every affine scheme over the base. -/
theorem iff_forall_affine_kernelPresentation :
    SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        affineEvaluationUnderlying ℱ ↔
      ∀ (U : Over S) [IsAffine U.left],
        HasQuasicoherentKernelPresentation
          ((@RingedSite.Hom.modulePullback _ _
            (StandardTopology.Big.pullbackRingedHom τ U.hom)
            (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
              τ U.hom)).obj ℱ) := sorry

end IsAdequate

end SheafOfModules
