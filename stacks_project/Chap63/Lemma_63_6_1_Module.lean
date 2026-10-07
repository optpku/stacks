module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_6_1_UpperShriek

/-!
# Module-valued non-derived upper shriek

The right adjoint `f^!` of compact-support `f_!` on étale sheaves of
`Λ`-modules, together with the mate isomorphism comparing it with the abelian
`f^!` after `sheafCompose` of `forget₂ ModuleCat AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compact-support direct image `f_!` on étale sheaves of `Λ`-modules is a left
adjoint. -/
instance lowerShriekModule_isLeftAdjoint : (lowerShriekModule f Λ).IsLeftAdjoint :=
  sorry

/-- The non-derived upper shriek `f^!` on étale sheaves of `Λ`-modules, the
chosen right adjoint of `lowerShriekModule`. -/
def upperShriekModule :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (lowerShriekModule f Λ).rightAdjoint

/-- `upperShriekModule f Λ` is the chosen right adjoint of
`lowerShriekModule f Λ`. -/
theorem upperShriekModule_def :
    upperShriekModule f Λ = (lowerShriekModule f Λ).rightAdjoint :=
  sorry

/-- The adjunction `f_! ⊣ f^!` on étale sheaves of `Λ`-modules. -/
def lowerShriekModuleAdjunction : lowerShriekModule f Λ ⊣ upperShriekModule f Λ :=
  Adjunction.ofIsLeftAdjoint (lowerShriekModule f Λ)

/-- The hom-equivalence of the module-valued compact-support adjunction. -/
def lowerShriekModuleAdjunction_homEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((lowerShriekModule f Λ).obj F ⟶ G) ≃ (F ⟶ (upperShriekModule f Λ).obj G) :=
  (lowerShriekModuleAdjunction f Λ).homEquiv F G

variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The functorial forgetful comparison of compact-support functors, assembled
from the objectwise isomorphisms `lowerShriekModule_forget`. -/
def lowerShriekModule_forgetNatTrans :
    lowerShriekModule f Λ ⋙
        sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⟶
      sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        lowerShriek f where
  app F := (lowerShriekModule_forget f Λ F).hom
  naturality := sorry

/-- The lower forgetful comparison of compact-support functors is an
isomorphism. -/
instance lowerShriekModule_forgetNatTrans_isIso :
    IsIso (lowerShriekModule_forgetNatTrans f Λ) :=
  sorry

/-- The mate of `lowerShriekModule_forgetNatTrans` along the module and abelian
compact-support adjunctions. -/
def upperShriekModule_forgetHom :
    upperShriekModule f Λ ⋙
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⟶
      sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        upperShriek f :=
  mateEquiv (lowerShriekModuleAdjunction f Λ) (lowerShriekAdjunction f)
    (inv (lowerShriekModule_forgetNatTrans f Λ))

/-- The upper forgetful comparison is an isomorphism. -/
instance upperShriekModule_forgetHom_isIso :
    IsIso (upperShriekModule_forgetHom f Λ) :=
  sorry

/-- The module-valued `f^!` agrees with the abelian `f^!` on underlying abelian
sheaves. -/
def upperShriekModule_forget :
    upperShriekModule f Λ ⋙
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        upperShriek f :=
  asIso (upperShriekModule_forgetHom f Λ)

/-- The forward map of `upperShriekModule_forget` is the constructed mate. -/
theorem upperShriekModule_forget_hom :
    (upperShriekModule_forget f Λ).hom = upperShriekModule_forgetHom f Λ :=
  sorry

/-- `upperShriekModule_forget` evaluated at a sheaf of `Λ`-modules. -/
def upperShriekModule_forget_app
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((upperShriekModule f Λ).obj G) ≅
      (upperShriek f).obj
        ((sheafCompose Y.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) :=
  (upperShriekModule_forget f Λ).app G

end AlgebraicGeometry.Scheme.Etale

end
