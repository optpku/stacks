/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A sectionwise scalar-compatible additive sheaf morphism lifts to a module
sheaf morphism with the same underlying maps. -/
def liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hα : ∀ (U : S.Etaleᵒᵖ) (r : Λ) (x : F.obj.obj U),
      (α.hom.app U).hom (r • x) = HSMul.hSMul (α := Λ) (β := G.obj.obj U) (γ := G.obj.obj U)
        r ((α.hom.app U).hom x)) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} Λ)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := hα U }
      naturality := sorry }

/-- The lift recovers the original abelian sheaf morphism after forgetting
coefficients. -/
theorem sheafCompose_map_liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u}
    [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hα : ∀ (U : S.Etaleᵒᵖ) (r : Λ) (x : F.obj.obj U),
      (α.hom.app U).hom (r • x) = HSMul.hSMul (α := Λ) (β := G.obj.obj U) (γ := G.obj.obj U)
        r ((α.hom.app U).hom x)) :
    (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        (liftModuleSheafHom α hα) =
      α :=
  sorry

/-- Functorial forgetful comparison of compact-support functors, assembled
from the objectwise isomorphisms `lowerShriekModule_forget`. -/
def lowerShriekModule_forgetFunctorIso {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    lowerShriekModule h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        lowerShriek h :=
  asIso (lowerShriekModule_forgetNatTrans h Λ)

/-- The objectwise forgetful comparison is the component of
`lowerShriekModule_forgetFunctorIso`. -/
theorem lowerShriekModule_forgetFunctorIso_app {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule_forgetFunctorIso h Λ).app F =
      lowerShriekModule_forget h Λ F :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
