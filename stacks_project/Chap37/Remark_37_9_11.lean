module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation.Compatibility
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

open RingedSpace.Hom

namespace Scheme.Hom
namespace Deformation

/- Remark 37.9.11: perturbing the horizontal morphisms in compatible diagrams of
first-order thickenings preserves the primed commutative square, without assuming the
morphisms between the schemes or bases are étale, provided the two perturbation maps are
compatible under the canonical differential and conormal comparisons.
-/
@[stacks 04BZ] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.perturbation_commSq_of_compatible :
    ∀ (S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u})
    (i₁ : T₁ ⟶ T₁') (j₁ : X₁ ⟶ X₁') (a₁ : T₁ ⟶ X₁)
    (a₁' : T₁' ⟶ X₁') (i₂ : T₂ ⟶ T₂') (j₂ : X₂ ⟶ X₂')
    (a₂ : T₂ ⟶ X₂) (a₂' : T₂' ⟶ X₂')
    (h : T₂ ⟶ T₁) (h' : T₂' ⟶ T₁')
    (f : X₂ ⟶ X₁) (f' : X₂' ⟶ X₁') (s : S₂ ⟶ S₁)
    [T₁.Over S₁] [T₁'.Over S₁] [X₁.Over S₁] [X₁'.Over S₁]
    [T₂.Over S₂] [T₂'.Over S₂] [X₂.Over S₂] [X₂'.Over S₂]
    [i₁.IsOver S₁] [j₁.IsOver S₁] [a₁.IsOver S₁] [a₁'.IsOver S₁]
    [i₂.IsOver S₂] [j₂.IsOver S₂] [a₂.IsOver S₂] [a₂'.IsOver S₂]
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening j₁]
    [IsFirstOrderThickening i₂] [IsFirstOrderThickening j₂]
    (sqA₁ : CommSq a₁ i₁ j₁ a₁') (sqA₂ : CommSq a₂ i₂ j₂ a₂')
    (sqT : CommSq h i₂ i₁ h') (sqX : CommSq f j₂ j₁ f')
    (sq₀ : CommSq a₂ h f a₁) (sq₁ : CommSq a₂' h' f' a₁')
    (sqS : CommSq f' (X₂' ↘ S₂) (X₁' ↘ S₁) s)
    (theta₁ : (Scheme.Modules.pullback a₁).obj Ω[(X₁ ↘ S₁).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₁)
    (theta₂ : (Scheme.Modules.pullback a₂).obj Ω[(X₂ ↘ S₂).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₂)
    (b₁' : T₁' ⟶ X₁') (b₂' : T₂' ⟶ X₂')
    (hb₁ : IsPerturbation S₁ i₁ j₁ a₁ a₁' sqA₁ theta₁ b₁')
    (hb₂ : IsPerturbation S₂ i₂ j₂ a₂ a₂' sqA₂ theta₂ b₂')
    (sqTheta : CommSq
      (pullbackDifferentialsMap s f h a₁ a₂
        (baseCommSq s j₁ j₂ f f' sqX sqS) sq₀)
      ((Scheme.Modules.pullback h).map theta₁) theta₂ (Conormal.map sqT)),
    CommSq b₂' h' f' b₁')

end Deformation
end Scheme.Hom
end AlgebraicGeometry
