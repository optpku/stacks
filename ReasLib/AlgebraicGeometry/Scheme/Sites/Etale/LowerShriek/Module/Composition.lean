module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Separated

/-!
# Composition of module-valued étale lower shriek
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Forgetting coefficients identifies `g_! (f_! F)` with
`(etaleLowerShriek g) ((etaleLowerShriek f) (forget F))`. -/
def lowerShriekModuleCompIso_forgetLeft
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)) ≅
      (etaleLowerShriek g).obj
        ((etaleLowerShriek f).obj
          ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (lowerShriekModule_forgetFunctorIso g Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (lowerShriek g).mapIso
      ((lowerShriekModule_forgetFunctorIso f Λ).app F) ≪≫
    (lowerShriekIso_separated g).app
      ((lowerShriek f).obj
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) ≪≫
    (etaleLowerShriek g).mapIso
      ((lowerShriekIso_separated f).app
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))

/-- Forgetting coefficients identifies `(f ≫ g)_! F` with
`(etaleLowerShriek (f ≫ g)) (forget F)`. -/
def lowerShriekModuleCompIso_forgetRight
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule (f ≫ g) Λ).obj F) ≅
      (etaleLowerShriek (f ≫ g)).obj
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (lowerShriekModule_forgetFunctorIso (f ≫ g) Λ).app F ≪≫
    (lowerShriekIso_separated (f ≫ g)).app
      ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)

/-- The component of the module sheaf isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`
at a sheaf of `Λ`-modules. -/
def lowerShriekModuleCompIso_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriekModule (f ≫ g) Λ).obj F :=
  {
    hom :=
      liftModuleSheafHom
        ((lowerShriekModuleCompIso_forgetLeft f g Λ F).hom ≫
          ((etaleLowerShriekCompIso f g).app
              ((sheafCompose X.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          (lowerShriekModuleCompIso_forgetRight f g Λ F).inv) sorry
    inv :=
      liftModuleSheafHom
        ((lowerShriekModuleCompIso_forgetRight f g Λ F).hom ≫
          ((etaleLowerShriekCompIso f g).app
              ((sheafCompose X.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
          (lowerShriekModuleCompIso_forgetLeft f g Λ F).inv) sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }


/-- The sheaf-level module isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`. -/
def lowerShriekModuleCompIso :
    lowerShriekModule f Λ ⋙ lowerShriekModule g Λ ≅
      lowerShriekModule (f ≫ g) Λ :=
  NatIso.ofComponents (lowerShriekModuleCompIso_app f g Λ) sorry

/-- The forward map of `lowerShriekModuleCompIso` is assembled componentwise
from the abelian composition isomorphism after forgetting coefficients. -/
theorem lowerShriekModuleCompIso_hom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModuleCompIso f g Λ).hom.app F =
      (lowerShriekModuleCompIso_app f g Λ F).hom := sorry

end AlgebraicGeometry.Scheme.Etale

end
