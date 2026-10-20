/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.Sites.GlobalSections.Hom
public import ReasLib.CategoryTheory.Sites.Localization.Presheaf
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

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.CohomologyOverPresheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (G : Cᵒᵖ ⥤ Type (max w v))

/-- The tautological section of the pulled-back presheaf is compatible with restriction. -/
theorem tautologicalElementsSection_naturality
    {X Y : (G.Elementsᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    (Presheaf.terminal.{max w v} G.Elementsᵒᵖ).map f ≫
      TypeCat.ofHom (fun _ ↦ Y.unop.unop.snd) =
    TypeCat.ofHom (fun _ ↦ X.unop.unop.snd) ≫
      ((Presheaf.localizationForget G).op ⋙ G).map f := sorry

/-- The tautological section of `j⁻¹ G` on `C / G`. -/
def tautologicalElementsSection :
    Presheaf.terminal.{max w v} G.Elementsᵒᵖ ⟶
      (Presheaf.localizationForget G).op ⋙ G where
  app e := TypeCat.ofHom fun _ ↦ e.unop.unop.snd
  naturality _ _ f := tautologicalElementsSection_naturality G f

/-- Evaluating `tautologicalElementsSection` returns the tautological `G`-section. -/
theorem tautologicalElementsSection_app (e : (G.Elementsᵒᵖ)ᵒᵖ) :
    (tautologicalElementsSection G).app e PUnit.unit = e.unop.unop.snd :=
  rfl

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
        (J.freeAbelianSheaf.{max w v} G : Sheaf J AddCommGrpCat.{max w v}) :=
  (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).map
      (tautologicalFreeAbelian G) ≫
    ((Presheaf.localizationForget G).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{max w v} (Presheaf.localizationSite J G) J).hom.app
      (FreeAbelianPresheaf.obj G)

/-- The constant integer sheaf on `C / G` maps to `j⁻¹ Z_G` by the tautological generator. -/
def tautologicalConstantInteger :
    (constantIntegerSheaf.{max u v w, v, max w v} (Presheaf.localizationSite J G) :
      Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}) ⟶
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).obj
        (J.freeAbelianSheaf.{max w v} G : Sheaf J AddCommGrpCat.{max w v}) :=
  (presheafToSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}).map
      (((const (G.Elementsᵒᵖ)ᵒᵖ).mapIso freePUnitIsoInteger.symm).hom ≫
        (constComp (G.Elementsᵒᵖ)ᵒᵖ (PUnit : Type (max w v)) AddCommGrpCat.free).inv) ≫
    tautologicalFreeAbelianSheaf J G

/-- Pullback and precomposition with the tautological integer generator commute with
morphisms of coefficient sheaves. -/
theorem homFunctorLocalizationComparison_laws
    {F F' : Sheaf J AddCommGrpCat.{max w v}} (f : F ⟶ F')
    (h : J.freeAbelianSheaf.{max w v} G ⟶ F) :
    tautologicalConstantInteger J G ≫
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map (h ≫ f) =
    (tautologicalConstantInteger J G ≫
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map h) ≫
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map f := sorry

/-- The underived comparison from cohomology over a presheaf to cohomology on its localization. -/
def homFunctorLocalizationComparison :
    homFunctor.{w, v, u} J G ⟶
      Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
        globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G) where
  app F := AddCommGrpCat.ofHom
    ((Preadditive.leftComp _ (tautologicalConstantInteger J G)).comp
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).mapAddHom)
  naturality _ _ f := by
    ext h
    exact homFunctorLocalizationComparison_laws J G f h

/-- The underived localization comparison is pullback followed by the tautological generator. -/
theorem homFunctorLocalizationComparison_app
    (F : Sheaf J AddCommGrpCat.{max w v}) (f : J.freeAbelianSheaf.{max w v} G ⟶ F) :
    (homFunctorLocalizationComparison J G).app F f =
      tautologicalConstantInteger J G ≫
        (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).map f := rfl

variable [HasDerivedCategory.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w} AddCommGrpCat.{max u v w}]
variable [(homFunctor.{w, v, u} J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

variable [HasDerivedCategory.{max u v w}
    (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]

set_option maxHeartbeats 800000 in
/-- The bounded-below comparison from cohomology over a presheaf to derived global sections
of its exact derived inverse image on the localization site. -/
def rGammaOverPresheafLocalizationComparison :
    derivedFunctor.{max u v w, w, v, u} J G ⟶
      siteAbelianInverseImageBoundedBelowDerived.{max u v w, v, u, v, max w v, max u v w, max u v w} (Presheaf.localizationSite J G) J
        (Presheaf.localizationForget G) ⋙
      Functor.RightDerived.Bounded.functor
        (globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)) :=
  Functor.RightDerived.Bounded.map (homFunctorLocalizationComparison J G) ≫
    Functor.RightDerived.Composition.BoundedBelow.comparison
      (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v})
      (globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)) ≫
    whiskerRight
      (@ExactFunctor.Derived.Plus.rightDerivedIso _ _ _ _ _ _ _ _
        (siteAbelianInverseImageExact.{max u v w, v, u, v, max w v}
          (Presheaf.localizationSite J G) J (Presheaf.localizationForget G))
        (by
          change (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).toBoundedBelowDerived.HasRightDerivedFunctor
            (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))
          infer_instance)).hom
      (Functor.RightDerived.Bounded.functor
        (globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)))

/-- The canonical bounded-below cohomology comparison for localization at a presheaf
is an isomorphism on every coefficient complex. -/
instance rGammaOverPresheafLocalizationComparison_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    IsIso ((rGammaOverPresheafLocalizationComparison J G).app E) := sorry

end CategoryTheory.Sheaf.CohomologyOverPresheaf
