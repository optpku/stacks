/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity

/-!
# Forgetting coefficients on étale module sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Continuous small-étale module pushforward commutes with forgetting from
`Λ`-modules to abelian groups. -/
def modulePushforward_forgetAbelianIso {S T : Scheme.{u}} (h : S ⟶ T)
    (Λ : Type u) [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) T.smallEtaleTopology S.smallEtaleTopology) ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianPushforward h :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}) (Iso.refl _)

/-- Scalar compatibility of a specified abelian map between underlying module sheaves. -/
def etaleModuleSheafHomLinear {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) : Prop :=
  ∀ (U : S.Etaleᵒᵖ) (r : Λ) (x : F.obj.obj U),
    ((α.hom.app U).hom (r • x) : G.obj.obj U) =
      @SMul.smul Λ (G.obj.obj U) inferInstance r ((α.hom.app U).hom x)

/-- Rebundle the specified additive section maps only with their actual scalar law. -/
def liftEtaleModuleSheafHom {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hlinear : etaleModuleSheafHomLinear α) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} Λ)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := hlinear U }
      naturality := sorry }

/-- Scalar rebundling leaves the supplied section map unchanged. -/
theorem liftEtaleModuleSheafHom_apply {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hlinear : etaleModuleSheafHomLinear α) (U : S.Etaleᵒᵖ) (x : F.obj.obj U) :
    ((liftEtaleModuleSheafHom α hlinear).hom.app U).hom x = (α.hom.app U).hom x := rfl


end AlgebraicGeometry.Scheme.Etale

end
