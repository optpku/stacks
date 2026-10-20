module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation.Compatibility
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Differentials

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

/-- The canonical identification of the differential module pulled back along `a₂` with the
iterated pullback along `a₁` and `h`. -/
noncomputable def pullbackDifferentialsIso
    {S₁ S₂ T₁ T₂ X₁ X₂ : Scheme.{u}}
    (s : S₂ ⟶ S₁) (f : X₂ ⟶ X₁) (h : T₂ ⟶ T₁)
    (a₁ : T₁ ⟶ X₁) (a₂ : T₂ ⟶ X₂)
    [X₁.Over S₁] [X₂.Over S₂]
    (sqS : CommSq f (X₂ ↘ S₂) (X₁ ↘ S₁) s)
    (sqA : CommSq a₂ h f a₁) [Etale f] [Etale s] :
    (Scheme.Modules.pullback a₂).obj Ω[(X₂ ↘ S₂).toShHom] ≅
      (Scheme.Modules.pullback h).obj
        ((Scheme.Modules.pullback a₁).obj Ω[(X₁ ↘ S₁).toShHom]) :=
  (Scheme.Modules.pullback a₂).mapIso
      (@asIso _ _ _ _ (Differentials.comparison
        (sqS.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)))
        (Scheme.RelativeDifferentials.comparison_isIso_of_etale sqS)).symm ≪≫
    (Scheme.Modules.pullbackComp a₂ f).app Ω[(X₁ ↘ S₁).toShHom] ≪≫
    (Scheme.Modules.pullbackCongr sqA.w).app Ω[(X₁ ↘ S₁).toShHom] ≪≫
    ((Scheme.Modules.pullbackComp h a₁).app Ω[(X₁ ↘ S₁).toShHom]).symm

/-- The morphism of the canonical pullback-differentials identification is the composite of
the inverse étale comparison and the pullback coherence maps. -/
theorem pullbackDifferentialsIso_hom
    {S₁ S₂ T₁ T₂ X₁ X₂ : Scheme.{u}}
    (s : S₂ ⟶ S₁) (f : X₂ ⟶ X₁) (h : T₂ ⟶ T₁)
    (a₁ : T₁ ⟶ X₁) (a₂ : T₂ ⟶ X₂)
    [X₁.Over S₁] [X₂.Over S₂]
    (sqS : CommSq f (X₂ ↘ S₂) (X₁ ↘ S₁) s)
    (sqA : CommSq a₂ h f a₁) [Etale f] [Etale s] :
    (pullbackDifferentialsIso s f h a₁ a₂ sqS sqA).hom =
      (Scheme.Modules.pullback a₂).map
          (@asIso _ _ _ _ (Differentials.comparison
            (sqS.map (Scheme.forgetToLocallyRingedSpace ⋙
              LocallyRingedSpace.forgetToSheafedSpace)))
            (Scheme.RelativeDifferentials.comparison_isIso_of_etale sqS)).inv ≫
        (Scheme.Modules.pullbackComp a₂ f).hom.app Ω[(X₁ ↘ S₁).toShHom] ≫
        (Scheme.Modules.pullbackCongr sqA.w).hom.app Ω[(X₁ ↘ S₁).toShHom] ≫
        (Scheme.Modules.pullbackComp h a₁).inv.app Ω[(X₁ ↘ S₁).toShHom] := sorry

/-- The pullback of a perturbation map through an étale square of relative differentials and
a square of conormal sheaves. -/
noncomputable def pullbackPerturbationMap
    {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₂ : Scheme.{u}}
    (s : S₂ ⟶ S₁) (f : X₂ ⟶ X₁) (h : T₂ ⟶ T₁)
    (a₁ : T₁ ⟶ X₁) (a₂ : T₂ ⟶ X₂)
    (i₁ : T₁ ⟶ T₁') (i₂ : T₂ ⟶ T₂') (h' : T₂' ⟶ T₁')
    [X₁.Over S₁] [X₂.Over S₂]
    (sqS : CommSq f (X₂ ↘ S₂) (X₁ ↘ S₁) s)
    (sqA : CommSq a₂ h f a₁) (sqT : CommSq h i₂ i₁ h')
    [Etale f] [Etale s]
    (theta₁ : (Scheme.Modules.pullback a₁).obj Ω[(X₁ ↘ S₁).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₁) :
    (Scheme.Modules.pullback a₂).obj Ω[(X₂ ↘ S₂).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₂ :=
  (pullbackDifferentialsIso s f h a₁ a₂ sqS sqA).hom ≫
    (Scheme.Modules.pullback h).map theta₁ ≫ Conormal.map sqT

/-- The pullback perturbation map is the differential identification followed by the pulled
map and the conormal comparison. -/
theorem pullbackPerturbationMap_def
    {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₂ : Scheme.{u}}
    (s : S₂ ⟶ S₁) (f : X₂ ⟶ X₁) (h : T₂ ⟶ T₁)
    (a₁ : T₁ ⟶ X₁) (a₂ : T₂ ⟶ X₂)
    (i₁ : T₁ ⟶ T₁') (i₂ : T₂ ⟶ T₂') (h' : T₂' ⟶ T₁')
    [X₁.Over S₁] [X₂.Over S₂]
    (sqS : CommSq f (X₂ ↘ S₂) (X₁ ↘ S₁) s)
    (sqA : CommSq a₂ h f a₁) (sqT : CommSq h i₂ i₁ h')
    [Etale f] [Etale s]
    (theta₁ : (Scheme.Modules.pullback a₁).obj Ω[(X₁ ↘ S₁).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₁) :
    pullbackPerturbationMap s f h a₁ a₂ i₁ i₂ h' sqS sqA sqT theta₁ =
      (pullbackDifferentialsIso s f h a₁ a₂ sqS sqA).hom ≫
        (Scheme.Modules.pullback h).map theta₁ ≫ Conormal.map sqT := sorry

/-- Perturbations transported through an étale square preserve the commutative square of
ambient morphisms. -/
theorem perturbation_commSq_of_etale
    (S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u})
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
    [IsFirstOrderThickening i₂] [IsFirstOrderThickening j₂] [Etale f] [Etale s]
    (sqA₁ : CommSq a₁ i₁ j₁ a₁') (sqA₂ : CommSq a₂ i₂ j₂ a₂')
    (sqT : CommSq h i₂ i₁ h') (sqX : CommSq f j₂ j₁ f')
    (sq₀ : CommSq a₂ h f a₁) (sq₁ : CommSq a₂' h' f' a₁')
    (sqS : CommSq f' (X₂' ↘ S₂) (X₁' ↘ S₁) s)
    (theta₁ : (Scheme.Modules.pullback a₁).obj Ω[(X₁ ↘ S₁).toShHom] ⟶
      Scheme.Hom.conormalSheaf i₁)
    (b₁' : T₁' ⟶ X₁') (b₂' : T₂' ⟶ X₂')
    (hb₁ : IsPerturbation S₁ i₁ j₁ a₁ a₁' sqA₁ theta₁ b₁')
    (hb₂ : IsPerturbation S₂ i₂ j₂ a₂ a₂' sqA₂
      (pullbackPerturbationMap s f h a₁ a₂ i₁ i₂ h'
        (baseCommSq s j₁ j₂ f f' sqX sqS) sq₀ sqT theta₁) b₂') :
    CommSq b₂' h' f' b₁' := sorry

end Deformation
end Scheme.Hom
end AlgebraicGeometry
