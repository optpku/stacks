module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ModulePullback

/-!
# Pro-étale base change of module sheaves

Base change of weakly étale objects along an arbitrary scheme morphism, and the
induced inverse image of sheaves of modules on small pro-étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Y X : Scheme.{u}}

#check (AlgebraicGeometry.Scheme.ProEt.baseChange :
    ∀ (f : Y ⟶ X),
      X.ProEt ⥤ Y.ProEt)

#check (AlgebraicGeometry.Scheme.ProEt.baseChange_def :
    ∀ (f : Y ⟶ X),
      baseChange f = MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)

#check (AlgebraicGeometry.Scheme.ProEt.baseChange_isContinuous :
    ∀ (f : Y ⟶ X),
      Functor.IsContinuous (baseChange f) (topology X) (topology Y))

#check (AlgebraicGeometry.Scheme.ProEt.baseChange_comp :
    ∀ {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X),
      baseChange (g ≫ f) ≅ baseChange f ⋙ baseChange g)

#check (AlgebraicGeometry.Scheme.ProEt.baseChange_id :
    baseChange (𝟙 X) ≅ 𝟭 X.ProEt)

variable {Λ : Type w} [Ring Λ]

#check (AlgebraicGeometry.Scheme.ProEt.modulePullback :
    ∀ (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)],
      Sheaf (topology X) (ModuleCat.{w} Λ) ⥤ Sheaf (topology Y) (ModuleCat.{w} Λ))

#check (AlgebraicGeometry.Scheme.ProEt.modulePullback_def :
    ∀ (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)],
      modulePullback f =
      (baseChange f).sheafPullback (ModuleCat.{w} Λ) (topology X) (topology Y))

#check (AlgebraicGeometry.Scheme.ProEt.moduleRestrict :
    ∀ (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    (F : Sheaf (topology X) (ModuleCat.{w} Λ)),
      Sheaf (topology Y) (ModuleCat.{w} Λ))

#check (AlgebraicGeometry.Scheme.ProEt.moduleRestrict_def :
    ∀ (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    (F : Sheaf (topology X) (ModuleCat.{w} Λ)),
      moduleRestrict f F = (modulePullback f).obj F)

#check (AlgebraicGeometry.Scheme.ProEt.modulePullback_comp :
    ∀ {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [∀ P : Y.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange g).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (g ≫ f)).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasWeakSheafify (topology Z) (ModuleCat.{w} Λ)],
      (modulePullback (g ≫ f) :
        Sheaf (topology X) (ModuleCat.{w} Λ) ⥤
          Sheaf (topology Z) (ModuleCat.{w} Λ)) ≅
      (modulePullback f :
          Sheaf (topology X) (ModuleCat.{w} Λ) ⥤
            Sheaf (topology Y) (ModuleCat.{w} Λ)) ⋙
        (modulePullback g :
          Sheaf (topology Y) (ModuleCat.{w} Λ) ⥤
            Sheaf (topology Z) (ModuleCat.{w} Λ)))

#check (AlgebraicGeometry.Scheme.ProEt.modulePullback_id :
    ∀ [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (𝟙 X)).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)],
      modulePullback (𝟙 X) ≅ 𝟭 (Sheaf (topology X) (ModuleCat.{w} Λ)))

end AlgebraicGeometry.Scheme.ProEt
