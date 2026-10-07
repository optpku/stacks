module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Remark_63_3_14_Comparison

/-!
# Composition of module and derived étale lower shriek

The Lemma 63.3.13 identification `f_! ⋙ g_! ≅ (f ≫ g)_!` on abelian étale
sheaves lifts to sheaves of `Λ`-modules and then to `D(-, Λ)`.
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
variable (Λ : Type u) [CommRing Λ]
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
    (lowerShriekIsoEtaleLowerShriek g).app
      ((lowerShriek f).obj
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) ≪≫
    (etaleLowerShriek g).mapIso
      ((lowerShriekIsoEtaleLowerShriek f).app
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
    (lowerShriekIsoEtaleLowerShriek (f ≫ g)).app
      ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)

/-- The component of the module sheaf isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`
at a sheaf of `Λ`-modules. -/
def lowerShriekModuleCompIso_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriekModule (f ≫ g) Λ).obj F where
  hom :=
    liftModuleSheafHom
      ((lowerShriekModuleCompIso_forgetLeft f g Λ F).hom ≫
        ((etaleLowerShriekCompIso f g).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (lowerShriekModuleCompIso_forgetRight f g Λ F).inv)
  inv :=
    liftModuleSheafHom
      ((lowerShriekModuleCompIso_forgetRight f g Λ F).hom ≫
        ((etaleLowerShriekCompIso f g).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
        (lowerShriekModuleCompIso_forgetLeft f g Λ F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

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
      (lowerShriekModuleCompIso_app f g Λ F).hom :=
  sorry

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived compact-support identification
`f_! ⋙ g_! ≅ (f ≫ g)_!` on `D(-, Λ)`. -/
def lowerShriekModuleDerivedCompIso :
    lowerShriekModuleDerived f Λ ⋙ lowerShriekModuleDerived g Λ ≅
      lowerShriekModuleDerived (f ≫ g) Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (lowerShriekModule f Λ))
      (ExactFunctor.of (lowerShriekModule g Λ))).symm ≪≫
    Functor.MapDerivedCategory.functorIso (lowerShriekModuleCompIso f g Λ)

/-- The forward map of `lowerShriekModuleDerivedCompIso` is the exact-derived
composition comparison conjugated by `mapDerivedCategory` of
`lowerShriekModuleCompIso`. -/
theorem lowerShriekModuleDerivedCompIso_hom :
    (lowerShriekModuleDerivedCompIso f g Λ).hom =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (lowerShriekModule f Λ))
          (ExactFunctor.of (lowerShriekModule g Λ))).symm.hom ≫
        (Functor.MapDerivedCategory.functorIso
          (lowerShriekModuleCompIso f g Λ)).hom :=
  sorry

/-- The derived composition identification at an object of `D(X_étale, Λ)`. -/
def lowerShriekModuleDerivedCompIso_app (K : EtaleDerived X Λ) :
    (lowerShriekModuleDerived g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj K) ≅
      (lowerShriekModuleDerived (f ≫ g) Λ).obj K :=
  (lowerShriekModuleDerivedCompIso f g Λ).app K

end AlgebraicGeometry.Scheme.Etale

end
