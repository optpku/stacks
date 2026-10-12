/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Derived
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
public import ReasLib.CategoryTheory.Functor.FreeAbelian
public import stacks_project.Chap85.Lemma_85_16_1_Localization
public import stacks_project.Chap85.Remark_85_17_6_Hypercovering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived comparisons for a hypercovering of a presheaf

Canonical `D⁺` comparison morphisms identify cohomology over a presheaf `G`, cohomology on
`C / G`, and cohomology on the total site of a hypercovering of `G`. Site-level `RΓ` is the
bounded derived functor of `Sheaf.Γ`; Hom out of the constant integer sheaf is only an internal
bridge into that universe of morphism groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open CategoryTheory.HypercoveringOf
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.CohomologyOverPresheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (G : Cᵒᵖ ⥤ Type (max w v))

/-- The tautological section of `j⁻¹ G` on `C / G`. -/
def tautologicalElementsSection :
    Presheaf.terminal.{max w v} G.Elementsᵒᵖ ⟶
      (Presheaf.localizationForget G).op ⋙ G where
  app e := TypeCat.ofHom fun _ ↦ e.unop.unop.snd
  naturality := sorry

/-- Evaluating `tautologicalElementsSection` returns the tautological `G`-section. -/
theorem tautologicalElementsSection_app (e : (G.Elementsᵒᵖ)ᵒᵖ) :
    (tautologicalElementsSection G).app e PUnit.unit = e.unop.unop.snd :=
  sorry

/-- The free-abelian tautological map on presheaves over `C / G`. -/
def tautologicalFreeAbelian :
    FreeAbelianPresheaf.obj (Presheaf.terminal.{max w v} G.Elementsᵒᵖ) ⟶
      (Presheaf.localizationForget G).op ⋙ FreeAbelianPresheaf.obj G :=
  (FreeAbelianPresheaf.homEquiv
      (Presheaf.terminal.{max w v} G.Elementsᵒᵖ)
      ((Presheaf.localizationForget G).op ⋙ FreeAbelianPresheaf.obj G)).symm
    (tautologicalElementsSection G ≫
      whiskerLeft (Presheaf.localizationForget G).op
        ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).unit.app G))

/-- `tautologicalFreeAbelian` is the free-forgetful adjunct of the tautological section. -/
theorem tautologicalFreeAbelian_eq :
    tautologicalFreeAbelian G =
      (FreeAbelianPresheaf.homEquiv
          (Presheaf.terminal.{max w v} G.Elementsᵒᵖ)
          ((Presheaf.localizationForget G).op ⋙ FreeAbelianPresheaf.obj G)).symm
        (tautologicalElementsSection G ≫
          whiskerLeft (Presheaf.localizationForget G).op
            ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).unit.app G)) :=
  sorry

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasWeakSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [∀ P : (G.Elementsᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{max w v},
    (Presheaf.localizationForget G).op.HasPointwiseRightKanExtension P]

/-- The sheaf morphism obtained by sheafifying `tautologicalFreeAbelian`. -/
def tautologicalFreeAbelianSheaf :
    (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).obj
        (FreeAbelianPresheaf.obj (Presheaf.terminal.{max w v} G.Elementsᵒᵖ)) ⟶
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).obj
        (J.freeAbelianSheaf G) :=
  (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).map
      (tautologicalFreeAbelian G) ≫
    ((Presheaf.localizationForget G).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{max w v} (Presheaf.localizationSite J G) J).hom.app
      (FreeAbelianPresheaf.obj G)

/-- The constant integer sheaf on `C / G` maps to `j⁻¹ Z_G` by the tautological generator. -/
def tautologicalConstantInteger :
    constantIntegerSheaf (Presheaf.localizationSite J G) ⟶
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).obj
        (J.freeAbelianSheaf G) :=
  (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).map
      (((const (G.Elementsᵒᵖ)ᵒᵖ).mapIso freePUnitIsoInteger.symm).hom ≫
        (constComp (G.Elementsᵒᵖ)ᵒᵖ (PUnit : Type (max w v)) AddCommGrpCat.free).inv) ≫
    tautologicalFreeAbelianSheaf J G

/-- `tautologicalConstantInteger` sheafifies the free-on-terminal comparison. -/
theorem tautologicalConstantInteger_eq :
    tautologicalConstantInteger J G =
      (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).map
          (((const (G.Elementsᵒᵖ)ᵒᵖ).mapIso freePUnitIsoInteger.symm).hom ≫
            (constComp (G.Elementsᵒᵖ)ᵒᵖ (PUnit : Type (max w v)) AddCommGrpCat.free).inv) ≫
        tautologicalFreeAbelianSheaf J G :=
  sorry

/-- Hom from the constant integer sheaf as the internal bridge for underived `H⁰(C / G, -)`. -/
abbrev localizationHomFunctor :
    Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max u v w} :=
  preadditiveCoyoneda.obj
    (op (constantIntegerSheaf (Presheaf.localizationSite J G)))

/-- `localizationHomFunctor` is Hom out of the constant integer sheaf on `C / G`. -/
theorem localizationHomFunctor_eq :
    localizationHomFunctor J G =
      preadditiveCoyoneda.obj
        (op (constantIntegerSheaf (Presheaf.localizationSite J G))) :=
  sorry

/-- Underived comparison `H⁰(G, -) ⟶ H⁰(C / G, j⁻¹ -)`. -/
def homFunctorLocalizationComparison :
    homFunctor J G ⟶
      Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
        localizationHomFunctor J G where
  app F :=
    AddCommGrpCat.ofHom
      { toFun := fun f ↦
          tautologicalConstantInteger J G ≫
            (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map f
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- Applying `homFunctorLocalizationComparison` is tautological precomposition. -/
theorem homFunctorLocalizationComparison_app
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    (homFunctorLocalizationComparison J G).app F =
      AddCommGrpCat.ofHom
        { toFun := fun f ↦
            tautologicalConstantInteger J G ≫
              (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map f
          map_zero' := sorry
          map_add' := sorry } :=
  sorry

variable [HasDerivedCategory.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w} AddCommGrpCat.{max u v w}]
variable [(homFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      localizationHomFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

/-- Canonical `D⁺` comparison `RΓ(G, -) ⟶ R(j⁻¹ ⋙ Γ(C / G, -))`. -/
def rGammaOverPresheafLocalizationComparison :
    derivedFunctor J G ⟶
      Functor.RightDerived.Bounded.functor
        (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
          localizationHomFunctor J G) :=
  Functor.RightDerived.Bounded.map (homFunctorLocalizationComparison J G)

variable (K : HypercoveringOf J G)

/-- The canonical augmentation functor `a : ((C / G) / K)_total ⥤ C / G`. -/
abbrev augmentationForget :
    Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)) ⥤ G.Elementsᵒᵖ :=
  totalForget (toLocalizedSimplicial J K)

/-- `augmentationForget` is `totalForget` of the converted simplicial family. -/
theorem augmentationForget_eq :
    augmentationForget J G K = totalForget (toLocalizedSimplicial J K) :=
  sorry

/-- The composite `g = a ⋙ j` is localization of the converted total site. -/
theorem augmentationForget_comp_localizationForget :
    augmentationForget J G K ⋙ Presheaf.localizationForget G =
      totalForget (toLocalizedSimplicial J K) ⋙ Presheaf.localizationForget G :=
  sorry

/-- Inverse image along the converted total-site augmentation `a`. -/
abbrev localizedInverseImage :
    Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⥤
      Sheaf
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        AddCommGrpCat.{max w v} :=
  (augmentationForget J G K).sheafPushforwardContinuous AddCommGrpCat.{max w v}
    (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
    (Presheaf.localizationSite J G)

/-- `localizedInverseImage` is continuous sheaf pushforward of `augmentationForget`. -/
theorem localizedInverseImage_eq :
    localizedInverseImage J G K =
      (augmentationForget J G K).sheafPushforwardContinuous AddCommGrpCat.{max w v}
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        (Presheaf.localizationSite J G) :=
  sorry

/-- Inverse image along `g = a then j`. -/
abbrev totalInverseImage :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      Sheaf
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        AddCommGrpCat.{max w v} :=
  Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
    localizedInverseImage J G K

/-- `totalInverseImage` is `a⁻¹ ∘ j⁻¹`. -/
theorem totalInverseImage_eq :
    totalInverseImage J G K =
      Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
        localizedInverseImage J G K :=
  sorry

variable [HasWeakSheafify
    (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [HasSheafify
    (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [∀ P : (Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)))ᵒᵖ ⥤
      AddCommGrpCat.{max w v},
    (augmentationForget J G K).op.HasPointwiseRightKanExtension P]

/-- Inverse image along `a` preserves constant abelian sheaves. -/
def localizedConstantSheafCompInverseImageIso :
    constantSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⋙
      localizedInverseImage J G K ≅
    constantSheaf
      (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
      AddCommGrpCat.{max w v} :=
  (associator (const (G.Elementsᵒᵖ)ᵒᵖ)
      (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})
      (localizedInverseImage J G K)).symm ≪≫
    isoWhiskerLeft (const (G.Elementsᵒᵖ)ᵒᵖ)
      ((augmentationForget J G K).pushforwardContinuousSheafificationCompatibility
          AddCommGrpCat.{max w v}
          (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
          (Presheaf.localizationSite J G)).symm ≪≫
    associator (const (G.Elementsᵒᵖ)ᵒᵖ)
      ((whiskeringLeft _ _ AddCommGrpCat.{max w v}).obj (augmentationForget J G K).op)
      (presheafToSheaf
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        AddCommGrpCat.{max w v}) ≪≫
    isoWhiskerRight
      (constCompWhiskeringLeftIso
        (Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)))ᵒᵖ
        (augmentationForget J G K).op)
      (presheafToSheaf
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        AddCommGrpCat.{max w v})

/-- Hom from the constant integer sheaf as the internal bridge for underived `H⁰` on the
converted total site. -/
abbrev totalHomFunctor :
    Sheaf
        (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))
        AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max u v w} :=
  preadditiveCoyoneda.obj
    (op (constantIntegerSheaf
      (overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K))))

/-- `totalHomFunctor` is Hom out of the constant integer sheaf on the converted total site. -/
theorem totalHomFunctor_eq :
    totalHomFunctor J G K =
      preadditiveCoyoneda.obj
        (op (constantIntegerSheaf
          (overSiteTotalTopology (Presheaf.localizationSite J G)
            (toLocalizedSimplicial J K)))) :=
  sorry

/-- Underived comparison `H⁰(C / G, -) ⟶ H⁰((C / K)_total, a⁻¹ -)`. -/
def gammaLocalizationInverseImageComparison :
    localizationHomFunctor J G ⟶
      localizedInverseImage J G K ⋙ totalHomFunctor J G K where
  app E :=
    AddCommGrpCat.ofHom
      { toFun := fun f ↦
          (localizedConstantSheafCompInverseImageIso J G K).inv.app
              (AddCommGrpCat.of (ULift.{max w v} ℤ)) ≫
            (localizedInverseImage J G K).map f
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- Applying `gammaLocalizationInverseImageComparison` is precomposition with the constant-sheaf
comparison. -/
theorem gammaLocalizationInverseImageComparison_app
    (E : Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}) :
    (gammaLocalizationInverseImageComparison J G K).app E =
      AddCommGrpCat.ofHom
        { toFun := fun f ↦
            (localizedConstantSheafCompInverseImageIso J G K).inv.app
                (AddCommGrpCat.of (ULift.{max w v} ℤ)) ≫
              (localizedInverseImage J G K).map f
          map_zero' := sorry
          map_add' := sorry } :=
  sorry

variable [HasDerivedCategory.{max u v w}
    (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})]
variable [(localizationHomFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(localizedInverseImage J G K ⋙
      totalHomFunctor J G K).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      localizedInverseImage J G K ⋙
        totalHomFunctor J G K).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

/-- Canonical `D⁺` comparison `RΓ(C / G, -) ⟶ R(a⁻¹ ⋙ Γ((C / K)_total, -))`. -/
def rGammaLocalizationInverseImageComparison :
    Functor.RightDerived.Bounded.functor (localizationHomFunctor J G) ⟶
      Functor.RightDerived.Bounded.functor
        (localizedInverseImage J G K ⋙ totalHomFunctor J G K) :=
  Functor.RightDerived.Bounded.map (gammaLocalizationInverseImageComparison J G K)

/-- Canonical `D⁺` comparison `RΓ(G, -) ⟶ R(g⁻¹ ⋙ Γ((C / K)_total, -))`. -/
def rGammaOverPresheafTotalComparison :
    derivedFunctor J G ⟶
      Functor.RightDerived.Bounded.functor
        (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
          localizedInverseImage J G K ⋙ totalHomFunctor J G K) :=
  Functor.RightDerived.Bounded.map
    (homFunctorLocalizationComparison J G ≫
      whiskerLeft (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v})
        (gammaLocalizationInverseImageComparison J G K))

/-- Applying the underived total comparison after `j⁻¹` is whiskering. -/
theorem rGammaOverPresheafTotalComparison_underived_app
    (E : Sheaf J AddCommGrpCat.{max w v}) :
    (homFunctorLocalizationComparison J G ≫
        whiskerLeft (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v})
          (gammaLocalizationInverseImageComparison J G K)).app E =
      (homFunctorLocalizationComparison J G).app E ≫
        (gammaLocalizationInverseImageComparison J G K).app
          ((Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).obj E) :=
  sorry

end CategoryTheory.Sheaf.CohomologyOverPresheaf
