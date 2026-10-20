/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite

/-!
# Compact-support direct image for étale sheaves of modules

The functor `f_!` on sheaves of `Λ`-modules, obtained by sheafifying the
colimit of supported module sections `H_Z(F)` over admissible locally closed
subsets of `|X_V|`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The underlying abelian étale sheaf of a sheaf of `Λ`-modules. -/
def etaleModuleForget {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  (sheafCompose S.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F

/-- Forgetting coefficients is `sheafCompose` of `forget₂`. -/
theorem etaleModuleForget_obj {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleForget Λ F =
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F :=
  sorry

/-- The image of a module section in the underlying abelian étale sheaf. -/
def forgetModuleSection {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) {U : S.Etale}
    (σ : F.1.obj (op U)) : (etaleModuleForget Λ F).1.obj (op U) :=
  ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).map (𝟙 (F.1.obj (op U)))).hom σ

/-- Forgetting a module section applies `forget₂` on the identity of the section
module. -/
theorem forgetModuleSection_eq {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) {U : S.Etale}
    (σ : F.1.obj (op U)) :
    forgetModuleSection Λ F σ =
      ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).map
        (𝟙 (F.1.obj (op U)))).hom σ :=
  sorry

/-- The `Λ`-submodule `H_Z(F)` of sections of an étale sheaf of modules whose
support lies in a locally closed subset `Z` that is closed in the ambient open
`U`. -/
def moduleSectionsSupportedIn
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) {W : Scheme.{u}}
    (hW : W ⟶ X) [Etale hW] (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W))) :
    Submodule Λ (F.1.obj (op (mk (U.ι ≫ hW)))) where
  carrier :=
    {σ |
      U.ι ''
          (abelianSheafSectionSupport (etaleModuleForget Λ F)
            (mk (U.ι ≫ hW)) (forgetModuleSection Λ F σ) :
            Set (mk (U.ι ≫ hW)).left) ⊆
        (Z : Set W)}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in the module-valued `H_Z(F)` is containment of the image of the
étale section support in `Z`. -/
theorem mem_moduleSectionsSupportedIn_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) {W : Scheme.{u}}
    (hW : W ⟶ X) [Etale hW] (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (σ : F.1.obj (op (mk (U.ι ≫ hW)))) :
    σ ∈ moduleSectionsSupportedIn Λ F hW Z U h_subset h_closed ↔
      U.ι ''
          (abelianSheafSectionSupport (etaleModuleForget Λ F)
            (mk (U.ι ≫ hW)) (forgetModuleSection Λ F σ) :
            Set (mk (U.ι ≫ hW)).left) ⊆
        (Z : Set W) :=
  sorry

namespace FiniteSupport

/-- The module `H_Z(F)` of supported sections, as an object of `ModuleCat Λ`. -/
def moduleSections (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} (A : Admissible f V) : ModuleCat.{u} Λ :=
  ModuleCat.of Λ
    (moduleSectionsSupportedIn Λ F (baseChangeToSource f V) A.subset A.ambient
      A.subset_le_ambient A.isClosed_in_ambient)

/-- The compact-support module associated to an admissible support is `H_Z(F)`. -/
theorem moduleSections_eq (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} (A : Admissible f V) :
    moduleSections f Λ F A =
      ModuleCat.of Λ
        (moduleSectionsSupportedIn Λ F (baseChangeToSource f V) A.subset
          A.ambient A.subset_le_ambient A.isClosed_in_ambient) :=
  sorry

/-- Restriction of supported module sections along an inequality of admissible
supports. -/
def moduleSectionsMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} {A B : Admissible f V} (h : A ≤ B) :
    moduleSections f Λ F A ⟶ moduleSections f Λ F B :=
  ModuleCat.ofHom <|
    LinearMap.restrict (F.1.map (homOfLE (baseChangeToSource f V) h.2).op).hom
      (fun _ _ ↦ sorry)

/-- The diagram of `Λ`-modules `Z ↦ H_Z(F)` indexed by admissible supports on
`X_V`. -/
def moduleDiagram (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : Y.Etale) : Admissible f V ⥤ ModuleCat.{u} Λ where
  obj := moduleSections f Λ F
  map h := moduleSectionsMap f Λ F (leOfHom h)
  map_id := sorry
  map_comp := sorry

/-- The finite-support module diagram evaluates as `H_Z(F)` at an admissible
support. -/
theorem moduleDiagram_obj (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : Y.Etale) (A : Admissible f V) :
    (moduleDiagram f Λ F V).obj A = moduleSections f Λ F A :=
  sorry

/-- Restriction of supported module sections from `X_V` to `X_{V'}`. -/
def moduleRestriction (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {V' V : Y.Etale} (g : V' ⟶ V) :
    moduleDiagram f Λ F V ⟶
      Admissible.pullbackFunctor f g ⋙ moduleDiagram f Λ F V' where
  app A :=
    ModuleCat.ofHom <|
      LinearMap.restrict (F.1.map (preimageHom f g A.ambient).op).hom
        (fun _ _ ↦ sorry)
  naturality := sorry

/-- A morphism of étale sheaves of modules induces a morphism of finite-support
module diagrams. -/
def moduleMapDiagram {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)}
    (φ : F ⟶ G) (V : Y.Etale) :
    moduleDiagram f Λ F V ⟶ moduleDiagram f Λ G V where
  app A :=
    ModuleCat.ofHom <|
      LinearMap.restrict
        (φ.hom.app (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).hom
        (fun _ _ ↦ sorry)
  naturality := sorry

/-- Forgetting coefficients on supported module sections lands in the abelian
`H_Z`. -/
def moduleSections_forget (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} (A : Admissible f V) :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).obj
        (moduleSections f Λ F A) ⟶
      sections f (etaleModuleForget Λ F) A :=
  AddCommGrpCat.ofHom
    { toFun := fun
        (σ : moduleSectionsSupportedIn Λ F (baseChangeToSource f V) A.subset
            A.ambient A.subset_le_ambient A.isClosed_in_ambient) ↦
        ⟨σ.1, sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- Forgetting coefficients is natural in admissible supports. -/
def moduleDiagram_forget (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : Y.Etale) :
    moduleDiagram f Λ F V ⋙ forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u} ⟶
      diagram f (etaleModuleForget Λ F) V where
  app A := moduleSections_forget f Λ F A
  naturality := sorry

end FiniteSupport

/-- The presheaf `f_{p!}` of `Λ`-modules, sending `V` to the colimit of
`H_Z(F)` over admissible locally closed subsets of `|X_V|`. -/
def lowerShriekModulePresheaf :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj F :=
    { obj := fun V ↦ colimit (FiniteSupport.moduleDiagram f Λ F V.unop)
      map := fun {V W} g ↦
        colimMap (FiniteSupport.moduleRestriction f Λ F g.unop) ≫
          colimit.pre (FiniteSupport.moduleDiagram f Λ F W.unop)
            (FiniteSupport.Admissible.pullbackFunctor f g.unop)
      map_id := sorry
      map_comp := sorry }
  map {F G} φ :=
    { app := fun V ↦ colimMap (FiniteSupport.moduleMapDiagram f Λ φ V.unop)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Evaluating the compact-support module presheaf at `V` is the colimit of
`H_Z(F)` over admissible supports on `X_V`. -/
theorem lowerShriekModulePresheaf_obj_colimit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale) :
    ((lowerShriekModulePresheaf f Λ).obj F).obj (op V) =
      colimit (FiniteSupport.moduleDiagram f Λ F V) :=
  sorry

/-- Forgetting coefficients on the compact-support module presheaf lands in the
abelian compact-support presheaf. -/
def lowerShriekModulePresheaf_forget
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModulePresheaf f Λ).obj F ⋙
        forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u} ⟶
      (lowerShriekPresheaf f).obj (etaleModuleForget Λ F) where
  app V :=
    (preservesColimitIso (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
          (FiniteSupport.moduleDiagram f Λ F V.unop)).hom ≫
      colimMap (FiniteSupport.moduleDiagram_forget f Λ F V.unop)
  naturality := sorry

variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The direct image with compact support `f_!` on étale sheaves of `Λ`-modules,
obtained by sheafifying the module-valued presheaf `f_{p!}`. -/
def lowerShriekModule :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) :=
  lowerShriekModulePresheaf f Λ ⋙
    presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)

/-- Evaluating `f_!` on sheaves of `Λ`-modules sheafifies the compact-support
presheaf `f_{p!}`. -/
theorem lowerShriekModule_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f Λ).obj F =
      (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        ((lowerShriekModulePresheaf f Λ).obj F) :=
  sorry

variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The comparison morphism from the underlying abelian sheaf of `f_! F` to the
abelian compact-support image of the underlying abelian sheaf of `F`. -/
def lowerShriekModule_forgetHom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleForget Λ ((lowerShriekModule f Λ).obj F) ⟶
      (lowerShriek f).obj (etaleModuleForget Λ F) :=
  (sheafComposeNatIso Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
        (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u} Λ))
        (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u})).inv.app
      ((lowerShriekModulePresheaf f Λ).obj F) ≫
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
      (lowerShriekModulePresheaf_forget f Λ F)

/-- The forgetful comparison of compact-support functors is an isomorphism. -/
instance lowerShriekModule_forgetHom_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (lowerShriekModule_forgetHom f Λ F) :=
  sorry

/-- Forgetting from `Λ`-modules to abelian groups intertwines the compact-support
functors. -/
def lowerShriekModule_forget
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleForget Λ ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriek f).obj (etaleModuleForget Λ F) :=
  asIso (lowerShriekModule_forgetHom f Λ F)

/-- The forward map of `lowerShriekModule_forget` is the constructed forgetful
comparison. -/
theorem lowerShriekModule_forget_hom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule_forget f Λ F).hom =
      lowerShriekModule_forgetHom f Λ F :=
  sorry

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


end AlgebraicGeometry.Scheme.Etale

end
