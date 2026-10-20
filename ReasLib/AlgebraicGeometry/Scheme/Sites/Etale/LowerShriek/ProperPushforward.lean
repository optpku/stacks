/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Separated

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
variable (h_sq : CommSq g' f' f g)
variable [IsProper f] [IsProper f']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']

/-- The abelian sheaf isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!` obtained by
identifying proper pushforward with compact support and composing compact
support along the two paths of the commutative square. -/
def etaleLowerShriekPushforwardIso :
    etaleAbelianPushforward f' ⋙ etaleLowerShriek g ≅
      etaleLowerShriek g' ⋙ etaleAbelianPushforward f :=
  isoWhiskerRight (etaleLowerShriekIso f').symm (etaleLowerShriek g) ≪≫
    etaleLowerShriekCompIso f' g ≪≫
    (etaleLowerShriekCongr h_sq.w).symm ≪≫
    (etaleLowerShriekCompIso g' f).symm ≪≫
    isoWhiskerLeft (etaleLowerShriek g') (etaleLowerShriekIso f)

/-- The forward map of `etaleLowerShriekPushforwardIso` is the composite of
proper identifications, composition identifications, and transport along the
commutative square. -/
theorem etaleLowerShriekPushforwardIso_hom :
    (etaleLowerShriekPushforwardIso f f' g g' h_sq).hom =
      whiskerRight (etaleLowerShriekIso f').inv (etaleLowerShriek g) ≫
        (etaleLowerShriekCompIso f' g).hom ≫
        (etaleLowerShriekCongr h_sq.w).inv ≫
        (etaleLowerShriekCompIso g' f).inv ≫
        whiskerLeft (etaleLowerShriek g') (etaleLowerShriekIso f).hom :=
  rfl

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]

/-- Forgetting coefficients identifies `g_! (f'_* F)` with
`(etaleLowerShriek g) ((etaleAbelianPushforward f') (forget F))`. -/
def etaleModuleLowerShriekPushforward_forgetLeft
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule g Λ).obj ((etaleModulePushforward f' Λ).obj F)) ≅
      (etaleLowerShriek g).obj
        ((etaleAbelianPushforward f').obj
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (lowerShriekModule_forgetFunctorIso g Λ).app
      ((etaleModulePushforward f' Λ).obj F) ≪≫
    (lowerShriekIso_separated g).app
      ((sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward f' Λ).obj F)) ≪≫
    (etaleLowerShriek g).mapIso
      ((etaleModulePushforward_compSheafComposeIso f' Λ).app F)

/-- Forgetting coefficients identifies `f_* (g'_! F)` with
`(etaleAbelianPushforward f) ((etaleLowerShriek g') (forget F))`. -/
def etaleModuleLowerShriekPushforward_forgetRight
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward f Λ).obj ((lowerShriekModule g' Λ).obj F)) ≅
      (etaleAbelianPushforward f).obj
        ((etaleLowerShriek g').obj
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (etaleModulePushforward_compSheafComposeIso f Λ).app
      ((lowerShriekModule g' Λ).obj F) ≪≫
    (etaleAbelianPushforward f).mapIso
      ((lowerShriekModule_forgetFunctorIso g' Λ).app F ≪≫
        (lowerShriekIso_separated g').app
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))

/-- The component of the module sheaf isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!`
at a sheaf of `Λ`-modules. -/
def etaleModuleLowerShriekPushforwardIso_app
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj ((etaleModulePushforward f' Λ).obj F) ≅
      (etaleModulePushforward f Λ).obj ((lowerShriekModule g' Λ).obj F) := by
  refine {
    hom :=
      liftModuleSheafHom
        ((etaleModuleLowerShriekPushforward_forgetLeft f' g Λ F).hom ≫
          ((etaleLowerShriekPushforwardIso f f' g g' h_sq).app
              ((sheafCompose X'.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          (etaleModuleLowerShriekPushforward_forgetRight f g' Λ F).inv) ?_
    inv :=
      liftModuleSheafHom
        ((etaleModuleLowerShriekPushforward_forgetRight f g' Λ F).hom ≫
          ((etaleLowerShriekPushforwardIso f f' g g' h_sq).app
              ((sheafCompose X'.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
          (etaleModuleLowerShriekPushforward_forgetLeft f' g Λ F).inv) ?_
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  all_goals sorry

/-- The sheaf-level module isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!`. -/
def etaleModuleLowerShriekPushforwardIso :
    etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ ≅
      lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ :=
  NatIso.ofComponents
    (etaleModuleLowerShriekPushforwardIso_app f f' g g' h_sq Λ) sorry


end AlgebraicGeometry.Scheme.Etale

end
