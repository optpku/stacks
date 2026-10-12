/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom for module sheaves on a ringed site

The internal Hom is constructed explicitly as the sheaf whose sections over `U` are morphisms
between the restrictions to the slice site `C / U`.  Its module structure is induced by the
canonical action of `O(U)` on the target.  This explicit object, its functoriality, and the tensor
adjunction form the owner from which Mathlib's `Closed` and `MonoidalClosed` interfaces are
derived.

For a presheaf source, the mathematically natural extension is obtained by first applying module
sheafification.  The final section compares that construction with the canonical internal Hom.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)
open scoped CategoryTheory.MonoidalClosed

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Basic

variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable (O : Sheaf J CommRingCat.{max u v w})

/-- Morphisms between the restrictions of two module sheaves to the slice site over `U`.
Keeping all four inputs in the type head makes the canonical local-section module structure
available to instance search. -/
@[stacks 03EM "local morphisms on a slice"]
def LocalHom
    (O : Sheaf J CommRingCat.{max u v w})
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :=
  F.over U.unop ⟶ G.over U.unop

namespace LocalHom

/-- Local module-sheaf morphisms carry the canonical additive-group structure on morphisms in
an additive category. -/
@[stacks 03EM "additive group of local morphisms", implicit_reducible]
noncomputable instance instAddCommGroup
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    AddCommGroup (LocalHom O F G U) :=
  inferInstanceAs (AddCommGroup (F.over U.unop ⟶ G.over U.unop))

/-- Endomorphisms of the target act on local morphisms by postcomposition. -/
@[stacks 03EM "endomorphism action on local morphisms", implicit_reducible]
noncomputable instance instModuleEnd
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    Module (End (G.over U.unop)) (LocalHom O F G U) :=
  inferInstanceAs (Module (End (G.over U.unop)) (F.over U.unop ⟶ G.over U.unop))

end LocalHom

/-- The canonical `O(U)`-module structure on local morphisms `F|U ⟶ G|U`, induced by the
local-section action on the target. -/
@[stacks 03EM "module of local morphisms", implicit_reducible]
noncomputable instance homModule
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    Module (O.obj.obj U) (LocalHom O F G U) :=
  Module.compHom _ (SheafOfModules.sectionAction O G U.unop)

/-- Scalar multiplication on local morphisms is postcomposition with the local-section action
on the target. -/
@[simp, stacks 03EM "local-Hom scalar action"]
theorem smul_eq_comp
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (r : O.obj.obj U) (f : LocalHom O F G U) :
    r • f = f ≫ SheafOfModules.sectionActionHom O G U.unop r := sorry

namespace LocalHom

/-- Evaluate a local morphism on a section by terminal evaluation on the slice site. -/
noncomputable def evalFun
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (f : LocalHom O F G U) (x : F.val.obj U) : G.val.obj U :=
  SheafOfModules.sectionsOverEquiv G U.unop
    (SheafOfModules.sectionsMap f
      ((SheafOfModules.sectionsOverEquiv F U.unop).symm x))

/-- Evaluation of a local morphism is additive in the section. -/
theorem evalFun_add
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (f : LocalHom O F G U) (x x' : F.val.obj U) :
    evalFun O F G U f (x + x') =
      evalFun O F G U f x + evalFun O F G U f x' := sorry

/-- Evaluation of a local morphism is linear in the section. -/
theorem evalFun_smul
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (f : LocalHom O F G U) (r : O.obj.obj U) (x : F.val.obj U) :
    evalFun O F G U f (r • x) = r • evalFun O F G U f x := sorry

/-- Evaluation at a fixed local morphism as a linear map on sections. -/
noncomputable def evalRight
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (f : LocalHom O F G U) :
    F.val.obj U →ₗ[O.obj.obj U] G.val.obj U where
  toFun := evalFun O F G U f
  map_add' := evalFun_add O F G U f
  map_smul' := evalFun_smul O F G U f

/-- Linear evaluation is additive in the local morphism. -/
theorem evalRight_add
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (f g : LocalHom O F G U) :
    evalRight O F G U (f + g) =
      evalRight O F G U f + evalRight O F G U g := sorry

/-- Linear evaluation is linear in the local morphism. -/
theorem evalRight_smul
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (r : O.obj.obj U) (f : LocalHom O F G U) :
    evalRight O F G U (r • f) = r • evalRight O F G U f := sorry

/-- Evaluation as a bilinear map from local morphisms and sections. -/
@[stacks 03EM "evaluation of local morphisms"]
noncomputable def eval
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    LocalHom O F G U →ₗ[O.obj.obj U]
      F.val.obj U →ₗ[O.obj.obj U] G.val.obj U where
  toFun := evalRight O F G U
  map_add' := evalRight_add O F G U
  map_smul' := evalRight_smul O F G U

end LocalHom

/-- Restrict a local module-sheaf morphism along a morphism of the base site. -/
@[stacks 03EM "restriction of local module morphisms"]
noncomputable def restrictFun
    (F G : ringedSiteModuleCategory J O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    LocalHom O F G U → LocalHom O F G V :=
  fun f ↦
    (SheafOfModules.overFunctorMap (ringSheaf J O) i.unop).inv.app F ≫
      (SheafOfModules.overMap (ringSheaf J O) i.unop).map f ≫
        (SheafOfModules.overFunctorMap (ringSheaf J O) i.unop).hom.app G

/-- Restriction of local module-sheaf morphisms preserves addition. -/
theorem restrictFun_add
    (F G : ringedSiteModuleCategory J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (f g : LocalHom O F G U) :
    restrictFun O F G i (f + g) =
      restrictFun O F G i f + restrictFun O F G i g := sorry

/-- Restriction of local module-sheaf morphisms is semilinear over restriction of local
sections. -/
theorem restrictFun_smul
    (F G : ringedSiteModuleCategory J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : O.obj.obj U) (f : LocalHom O F G U) :
    restrictFun O F G i (r • f) = O.obj.map i r • restrictFun O F G i f := sorry

/-- The semilinear restriction map on modules of local morphisms. -/
@[stacks 03EM "linear restriction of local module morphisms"]
noncomputable def restrict
    (F G : ringedSiteModuleCategory J O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ModuleCat.of (O.obj.obj U) (LocalHom O F G U) ⟶
      (ModuleCat.restrictScalars (O.obj.map i).hom).obj
        (ModuleCat.of (O.obj.obj V) (LocalHom O F G V)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (O.obj.obj U) (LocalHom O F G U))
    (Y := (ModuleCat.restrictScalars (O.obj.map i).hom).obj
      (ModuleCat.of (O.obj.obj V) (LocalHom O F G V)))
    { toFun := restrictFun O F G i
      map_add' := restrictFun_add O F G i
      map_smul' := restrictFun_smul O F G i }

/-- Applying the bundled restriction map agrees with restriction of the underlying local
morphism. -/
@[simp]
theorem restrict_apply
    (F G : ringedSiteModuleCategory J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (f : LocalHom O F G U) :
    (restrict O F G i).hom f = restrictFun O F G i f := sorry

/-- Restriction of local morphisms respects identity arrows. -/
theorem restrict_id
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    restrict O F G (𝟙 U) =
      (ModuleCat.restrictScalarsId' (O.obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (O.obj.map_id U))).inv.app _ := sorry

/-- Restriction of local morphisms respects composition. -/
theorem restrict_comp
    (F G : ringedSiteModuleCategory J O) {U V W : Cᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    restrict O F G (i ≫ j) =
      restrict O F G i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (restrict O F G j) ≫
          (ModuleCat.restrictScalarsComp' (O.obj.map i).hom (O.obj.map j).hom
            (O.obj.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom (O.obj.map_comp i j))).inv.app _ := sorry

/-- The presheaf of modules of local morphisms from `F` to `G`. -/
@[stacks 03EM "internal-Hom module presheaf"]
noncomputable def presheaf
    (F G : ringedSiteModuleCategory J O) :
    PresheafOfModules (ringSheaf J O).obj where
  obj U := ModuleCat.of (O.obj.obj U) (LocalHom O F G U)
  map i := restrict O F G i
  map_id := restrict_id O F G
  map_comp := restrict_comp O F G

/-- The local-morphism module presheaf satisfies the sheaf condition. -/
theorem presheaf_isSheaf
    (F G : ringedSiteModuleCategory J O) :
    Presheaf.IsSheaf J (presheaf O F G).presheaf := sorry

/-- The internal-Hom module sheaf, with sections over `U` equal to `Hom(F|U, G|U)`. -/
@[stacks 03EM "internal-Hom module sheaf"]
noncomputable def obj
    (F G : ringedSiteModuleCategory J O) : ringedSiteModuleCategory J O where
  val := presheaf O F G
  isSheaf := presheaf_isSheaf O F G

/-- Sections of the internal-Hom sheaf over `U` are morphisms between the restrictions of its
source and target to `C / U`. -/
theorem obj_val_obj
    (F G : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    (obj O F G).val.obj U =
      ModuleCat.of (O.obj.obj U) (LocalHom O F G U) := sorry

/-- Postcompose a local morphism with the restriction of a global module-sheaf morphism. -/
noncomputable def postFun
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) :
    LocalHom O F G U → LocalHom O F H U :=
  fun f ↦ f ≫ g.over U.unop

/-- Postcomposition on local morphisms has the expected underlying formula. -/
@[simp]
theorem postFun_apply
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) (f : LocalHom O F G U) :
    postFun O F g U f = f ≫ g.over U.unop := sorry

/-- Postcomposition of local morphisms is additive. -/
theorem post_add
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ)
    (f f' : LocalHom O F G U) :
    postFun O F g U (f + f') = postFun O F g U f + postFun O F g U f' := sorry

/-- Postcomposition of local morphisms is linear over local sections. -/
theorem post_smul
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) (r : O.obj.obj U)
    (f : LocalHom O F G U) :
    postFun O F g U (r • f) = r • postFun O F g U f := sorry

/-- The objectwise linear map on local Homs induced by postcomposition. -/
noncomputable def post
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) :
    (presheaf O F G).obj U ⟶ (presheaf O F H).obj U :=
  ModuleCat.ofHom
    { toFun := postFun O F g U
      map_add' := post_add O F g U
      map_smul' := post_smul O F g U }

/-- Applying bundled postcomposition agrees with postcomposition of the underlying local
morphism. -/
@[simp]
theorem post_apply
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) (f : LocalHom O F G U) :
    (post O F g U).hom f = f ≫ g.over U.unop := sorry

/-- Postcomposition of local morphisms commutes with restriction. -/
theorem post_naturality
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (presheaf O F G).map i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (post O F g V) =
      post O F g U ≫ (presheaf O F H).map i := sorry

/-- The internal-Hom morphism induced by a morphism of targets. -/
noncomputable def map
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) : obj O F G ⟶ obj O F H where
  val :=
    { app U := post O F g U
      naturality := post_naturality O F g }

/-- The component of target functoriality is bundled local postcomposition. -/
@[simp]
theorem map_val_app
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) :
    (map O F g).val.app U = post O F g U := sorry

/-- Target functoriality acts on a local morphism by postcomposition. -/
@[simp]
theorem map_val_app_apply
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (U : Cᵒᵖ) (f : LocalHom O F G U) :
    ((map O F g).val.app U).hom f = f ≫ g.over U.unop := sorry

/-- Target functoriality of internal Hom preserves identity morphisms. -/
theorem map_id
    (F G : ringedSiteModuleCategory J O) :
    map O F (𝟙 G) = 𝟙 (obj O F G) := sorry

/-- Target functoriality of internal Hom preserves composition. -/
theorem map_comp
    (F : ringedSiteModuleCategory J O) {G H K : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (h : H ⟶ K) :
    map O F (g ≫ h) = map O F g ≫ map O F h := sorry

/-- Internal Hom from a fixed module sheaf as a functor in the target. -/
@[stacks 03EM "internal-Hom target functor"]
noncomputable def functor
    (F : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O where
  obj := obj O F
  map := map O F
  map_id := map_id O F
  map_comp := map_comp O F

/-- Evaluate an internal-Hom section on source sections over one object of the site. -/
noncomputable def sectionsToHomApp
    {F G : ringedSiteModuleCategory J O} (s : (obj O F G).sections) (U : Cᵒᵖ) :
    F.val.obj U ⟶ G.val.obj U :=
  ModuleCat.ofHom (X := F.val.obj U) (Y := G.val.obj U)
    (LocalHom.evalRight O F G U (s.val U))

/-- Evaluation of an internal-Hom section commutes with restriction. -/
theorem sectionsToHomApp_naturality
    {F G : ringedSiteModuleCategory J O} (s : (obj O F G).sections)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    F.val.map i ≫ (ModuleCat.restrictScalars (O.obj.map i).hom).map
        (sectionsToHomApp O s V) =
      sectionsToHomApp O s U ≫ G.val.map i := sorry

/-- The global module-sheaf morphism obtained by evaluating an internal-Hom section. -/
@[stacks 03EM "morphism classified by an internal-Hom section"]
noncomputable def sectionsToHom
    {F G : ringedSiteModuleCategory J O} (s : (obj O F G).sections) : F ⟶ G where
  val :=
    { app U := sectionsToHomApp O s U
      naturality := sectionsToHomApp_naturality O s }

/-- The morphism classified by an internal-Hom section restricts to the local morphism stored
by that section. -/
@[simp]
theorem sectionsToHom_over
    {F G : ringedSiteModuleCategory J O} (s : (obj O F G).sections) (U : Cᵒᵖ) :
    (sectionsToHom O s).over U.unop = s.val U := sorry

/-- Restrictions of a global module-sheaf morphism form a section of the internal-Hom sheaf. -/
theorem homToSections_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (obj O F G).val.map i (f.over U.unop) = f.over V.unop := sorry

/-- Regard a global module-sheaf morphism as the compatible family of all its restrictions. -/
@[stacks 03EM "internal-Hom section of a morphism"]
noncomputable def homToSections
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) : (obj O F G).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ f.over U.unop)
    (fun {_ _} i ↦ homToSections_naturality O f i)

/-- The value of the internal-Hom section associated to `f` is the restriction of `f`. -/
@[simp]
theorem homToSections_val
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) (U : Cᵒᵖ) :
    (homToSections O f).val U = f.over U.unop := sorry

/-- Converting an internal-Hom section to a morphism and back recovers the section. -/
theorem homToSections_sectionsToHom
    {F G : ringedSiteModuleCategory J O} (s : (obj O F G).sections) :
    homToSections O (sectionsToHom O s) = s := sorry

/-- Converting a morphism to an internal-Hom section and evaluating it recovers the morphism. -/
theorem sectionsToHom_homToSections
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    sectionsToHom O (homToSections O f) = f := sorry

/-- Global sections of the internal-Hom sheaf are canonically module-sheaf morphisms. -/
@[stacks 03EM "global sections of internal Hom"]
noncomputable def sectionsHomEquiv
    (F G : ringedSiteModuleCategory J O) :
    (obj O F G).sections ≃ (F ⟶ G) where
  toFun := sectionsToHom O
  invFun := homToSections O
  left_inv := homToSections_sectionsToHom O
  right_inv := sectionsToHom_homToSections O

/-- Applying the global-section equivalence is the explicit evaluation construction. -/
@[simp]
theorem sectionsHomEquiv_apply
    (F G : ringedSiteModuleCategory J O) (s : (obj O F G).sections) :
    sectionsHomEquiv O F G s = sectionsToHom O s := sorry

/-- The inverse global-section equivalence is the compatible family of restrictions. -/
@[simp]
theorem sectionsHomEquiv_symm_apply
    (F G : ringedSiteModuleCategory J O) (f : F ⟶ G) :
    (sectionsHomEquiv O F G).symm f = homToSections O f := sorry

/-- The morphism classified by an internal-Hom section restricts over `U` to the local
morphism represented by the value of that section at `U`. -/
@[simp]
theorem sectionsHomEquiv_apply_over
    (F G : ringedSiteModuleCategory J O) (s : (obj O F G).sections) (U : Cᵒᵖ) :
    (sectionsHomEquiv O F G s).over U.unop = s.val U := sorry

/-- The internal-Hom section corresponding to a module-sheaf morphism `f` has value
`f.over U.unop` over every object `U`. -/
@[simp]
theorem sectionsHomEquiv_symm_val
    (F G : ringedSiteModuleCategory J O) (f : F ⟶ G) (U : Cᵒᵖ) :
    ((sectionsHomEquiv O F G).symm f).val U = f.over U.unop := sorry

/-- The sections-to-Hom equivalence is natural under postcomposition in the target module
sheaf. -/
theorem sectionsHomEquiv_sectionsMap
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (s : (obj O F G).sections) :
    sectionsHomEquiv O F H (SheafOfModules.sectionsMap (map O F g) s) =
      sectionsHomEquiv O F G s ≫ g := sorry

/-- Passing a classified morphism through postcomposition agrees with mapping its
internal-Hom section along target functoriality. -/
theorem sectionsMap_sectionsHomEquiv_symm
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) (f : F ⟶ G) :
    SheafOfModules.sectionsMap (map O F g) ((sectionsHomEquiv O F G).symm f) =
      (sectionsHomEquiv O F H).symm (f ≫ g) := sorry

end Basic

section Closed

variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (O : Sheaf J CommRingCat.{max u v})
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

namespace Bilinear

/-- The objectwise bilinear evaluation associated to a morphism into internal Hom. -/
noncomputable def toBilinearApp
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G)
    (U : Cᵒᵖ) :
    F.val.obj U →ₗ[O.obj.obj U] H.val.obj U →ₗ[O.obj.obj U] G.val.obj U :=
  ((LocalHom.eval O F G U).comp (f.val.app U).hom).flip

/-- Bilinear evaluation of an internal-Hom morphism commutes with restriction. -/
theorem toBilinearApp_naturality
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : F.val.obj U) (y : H.val.obj U) :
    G.val.map i (toBilinearApp O f U x y) =
      toBilinearApp O f V (F.val.map i x) (H.val.map i y) := sorry

/-- A morphism into internal Hom determines a compatible sectionwise bilinear map. -/
@[stacks 03EM "evaluation into the local internal Hom"]
noncomputable def toBilinear
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G) :
    SectionBilinearMap O F H G where
  app := toBilinearApp O f
  naturality := toBilinearApp_naturality O f

/-- Evaluating the bilinear map associated to an internal-Hom morphism is evaluation of the
corresponding local morphism. -/
@[simp]
theorem toBilinear_app
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G)
    (U : Cᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (toBilinear O f).app U x y =
      LocalHom.evalFun O F G U ((f.val.app U).hom y) x := sorry

/-- Evaluate the local morphism curried from a bilinear map at one slice object. -/
noncomputable def localApply
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (x : (F.over U.unop).val.obj W) : (G.over U.unop).val.obj W :=
  b.app (Opposite.op W.unop.left) x
    (((SheafOfModules.sectionsOverEquiv H U.unop).symm y).1 W)

/-- Slice-wise curried evaluation is additive in the source section. -/
theorem localApply_add
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (x x' : (F.over U.unop).val.obj W) :
    localApply O b U y W (x + x') =
      localApply O b U y W x + localApply O b U y W x' := sorry

/-- Slice-wise curried evaluation is linear in the source section. -/
theorem localApply_smul
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (r : ((ringSheaf J O).over U.unop).obj.obj W)
    (x : (F.over U.unop).val.obj W) :
    localApply O b U y W (r • x) = r • localApply O b U y W x := sorry

/-- The component of the local morphism curried from a bilinear map. -/
noncomputable def localApp
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ) :
    (F.over U.unop).val.obj W ⟶ (G.over U.unop).val.obj W :=
  ModuleCat.ofHom
    (X := (F.over U.unop).val.obj W) (Y := (G.over U.unop).val.obj W)
    { toFun := localApply O b U y W
      map_add' := localApply_add O b U y W
      map_smul' := localApply_smul O b U y W }

/-- The components of a curried local morphism commute with restriction in the slice site. -/
theorem localApp_naturality
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) {W W' : (Over U.unop)ᵒᵖ} (i : W ⟶ W') :
    (F.over U.unop).val.map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O).over U.unop).obj.map i).hom).map
            (localApp O b U y W') =
      localApp O b U y W ≫ (G.over U.unop).val.map i := sorry

/-- The local morphism obtained by currying a bilinear map at one section. -/
noncomputable def localHom
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) : LocalHom O F G U where
  val :=
    { app W := localApp O b U y W
      naturality := localApp_naturality O b U y }

/-- Currying a bilinear map on a slice is additive in the fixed section. -/
theorem localHom_add
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y y' : H.val.obj U) :
    localHom O b U (y + y') = localHom O b U y + localHom O b U y' := sorry

/-- Currying a bilinear map on a slice is linear in the fixed section. -/
theorem localHom_smul
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (r : O.obj.obj U) (y : H.val.obj U) :
    localHom O b U (r • y) = r • localHom O b U y := sorry

/-- The objectwise linear map into internal Hom obtained from a bilinear map. -/
noncomputable def ofBilinearApp
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) : H.val.obj U ⟶ (obj O F G).val.obj U :=
  ModuleCat.ofHom
    (X := H.val.obj U) (Y := (obj O F G).val.obj U)
    { toFun := localHom O b U
      map_add' := localHom_add O b U
      map_smul' := localHom_smul O b U }

/-- Objectwise currying of a bilinear map commutes with restriction. -/
theorem ofBilinearApp_naturality
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    H.val.map i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (ofBilinearApp O b V) =
      ofBilinearApp O b U ≫ (obj O F G).val.map i := sorry

/-- A compatible sectionwise bilinear map curries to a morphism into internal Hom. -/
@[stacks 03EM "currying into the local internal Hom"]
noncomputable def ofBilinear
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G) :
    H ⟶ obj O F G where
  val :=
    { app U := ofBilinearApp O b U
      naturality := ofBilinearApp_naturality O b }

/-- The local morphism obtained by currying has the defining sectionwise evaluation formula. -/
@[simp]
theorem ofBilinear_app
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G)
    (U : Cᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (x : (F.over U.unop).val.obj W) :
    (((((ofBilinear O b).val.app U).hom y).val.app W).hom x) =
      localApply O b U y W x := sorry

/-- Evaluating a curried bilinear map recovers the original bilinear map. -/
@[simp]
theorem toBilinear_ofBilinear
    {F H G : ringedSiteModuleCategory J O} (b : SectionBilinearMap O F H G) :
    toBilinear O (ofBilinear O b) = b := sorry

/-- Currying the evaluation of an internal-Hom morphism recovers that morphism. -/
@[simp]
theorem ofBilinear_toBilinear
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G) :
    ofBilinear O (toBilinear O f) = f := sorry

/-- Compatible bilinear maps are canonically equivalent to morphisms into the local internal
Hom sheaf. -/
@[stacks 03EM "bilinear maps and local internal Hom"]
noncomputable def homEquiv
    (F H G : ringedSiteModuleCategory J O) :
    SectionBilinearMap O F H G ≃ (H ⟶ obj O F G) where
  toFun := ofBilinear O
  invFun := toBilinear O
  left_inv := toBilinear_ofBilinear O
  right_inv := ofBilinear_toBilinear O

end Bilinear

/-- The tensor/internal-Hom correspondence, obtained by combining the tensor product's
sectionwise bilinear universal property with currying into local Hom sheaves. -/
@[stacks 03EM "tensor and local internal Hom"]
noncomputable def homEquiv
    (F H G : ringedSiteModuleCategory J O) :
    (tensorObj F H ⟶ G) ≃ (H ⟶ obj O F G) :=
  (SectionBilinearMap.homEquiv
      (O := O) (F := F) (G := H) (H := G)).symm.trans
    (Bilinear.homEquiv O F H G)

/-- Uncurrying is natural in the variable tensored on the right. -/
theorem homEquiv_naturality_left_symm
    (F : ringedSiteModuleCategory J O)
    {H' H G : ringedSiteModuleCategory J O}
    (f : H' ⟶ H) (g : H ⟶ obj O F G) :
    (homEquiv O F H' G).symm (f ≫ g) =
      (tensorLeft F).map f ≫ (homEquiv O F H G).symm g := sorry

/-- Currying is natural in the target of the tensor morphism. -/
theorem homEquiv_naturality_right
    (F : ringedSiteModuleCategory J O)
    {H G G' : ringedSiteModuleCategory J O}
    (f : tensorObj F H ⟶ G) (g : G ⟶ G') :
    homEquiv O F H G' (f ≫ g) =
      homEquiv O F H G f ≫ (functor O F).map g := sorry

/-- The natural Hom-set equivalences exhibiting tensoring by `F` as a left adjoint. -/
@[stacks 03EM "tensor/internal-Hom adjunction data"]
noncomputable def coreHomEquiv
    (F : ringedSiteModuleCategory J O) :
    Adjunction.CoreHomEquiv (tensorLeft F) (functor O F) where
  homEquiv H G := homEquiv O F H G
  homEquiv_naturality_left_symm := homEquiv_naturality_left_symm O F
  homEquiv_naturality_right := homEquiv_naturality_right O F

/-- Tensoring by a module sheaf is left adjoint to its explicitly constructed internal-Hom
functor. -/
@[stacks 03EM "tensor/internal-Hom adjunction"]
noncomputable def adjunction
    (F : ringedSiteModuleCategory J O) :
    tensorLeft F ⊣ functor O F :=
  Adjunction.mkOfHomEquiv (coreHomEquiv O F)

/-- The canonical closed structure on a module sheaf, with right adjoint given by local Hom
sheaves. -/
@[stacks 03EM "closed module sheaf", implicit_reducible]
noncomputable def closed
    (F : ringedSiteModuleCategory J O) : Closed F where
  rightAdj := functor O F
  adj := adjunction O F

/-- The canonical monoidal closed structure on module sheaves over a commutative ringed site. -/
@[stacks 03EM "monoidal closed module sheaves", instance_reducible]
noncomputable def monoidalClosed :
    MonoidalClosed (ringedSiteModuleCategory J O) where
  closed := closed O

/-- Module sheaves on a commutative ringed site use the local-Hom sheaf as their canonical
internal Hom. -/
@[stacks 03EM "canonical internal Hom instance"]
noncomputable instance moduleMonoidalClosed :
    MonoidalClosed (ringedSiteModuleCategory J O) :=
  monoidalClosed O

/-- Mathlib's internal-Hom functor is the explicitly constructed local-Hom functor for the
canonical closed instance. -/
theorem ihom_eq_functor
    (F : ringedSiteModuleCategory J O) :
    ihom F = functor O F := sorry

/-- Mathlib's internal-Hom functor is definitionally the local-Hom functor for the canonical
closed instance. -/
@[simp]
theorem ihom_obj
    (F G : ringedSiteModuleCategory J O) :
    (ihom F).obj G = obj O F G := sorry

/-- Mathlib's internal-Hom functor acts on target morphisms by local postcomposition. -/
@[simp]
theorem ihom_map
    (F : ringedSiteModuleCategory J O) {G H : ringedSiteModuleCategory J O}
    (g : G ⟶ H) :
    (ihom F).map g = map O F g := sorry

/-- The Hom equivalence of the canonical tensor/internal-Hom adjunction is the explicit
sectionwise currying equivalence. -/
@[simp]
theorem adjunction_homEquiv
    (F H G : ringedSiteModuleCategory J O) :
    (adjunction O F).homEquiv H G = homEquiv O F H G := sorry

/-- Mathlib's canonical currying operation agrees with the explicit sectionwise currying
equivalence. -/
@[simp]
theorem curry_eq
    {F H G : ringedSiteModuleCategory J O} (f : tensorObj F H ⟶ G) :
    CategoryTheory.MonoidalClosed.curry f = homEquiv O F H G f := sorry

/-- Mathlib's canonical uncurrying operation agrees with the inverse explicit sectionwise
currying equivalence. -/
@[simp]
theorem uncurry_eq
    {F H G : ringedSiteModuleCategory J O} (f : H ⟶ obj O F G) :
    CategoryTheory.MonoidalClosed.uncurry f = (homEquiv O F H G).symm f := sorry

/-- Internal Hom from a module presheaf is the canonical internal Hom from its module
sheafification. -/
@[stacks 03EM "presheaf source"]
noncomputable abbrev fromPresheaf
    (F : PresheafOfModules (ringSheaf J O).obj)
    (G : ringedSiteModuleCategory J O) : ringedSiteModuleCategory J O :=
  (ihom ((moduleSheafification O).obj F)).obj G

/-- The forward map from internal Hom out of a sheafified underlying presheaf to the canonical
internal Hom out of the original module sheaf. -/
noncomputable def fromPresheafValHom
    (F G : ringedSiteModuleCategory J O) :
    fromPresheaf O F.val G ⟶ (ihom F).obj G :=
  (MonoidalClosed.pre (moduleSheafificationValIso O F).inv).app G

/-- The inverse map from the canonical internal Hom to internal Hom out of the sheafified
underlying presheaf. -/
noncomputable def fromPresheafValInv
    (F G : ringedSiteModuleCategory J O) :
    (ihom F).obj G ⟶ fromPresheaf O F.val G :=
  (MonoidalClosed.pre (moduleSheafificationValIso O F).hom).app G

/-- The explicit forward and inverse internal-Hom maps compose to the identity on the
sheafified-source internal Hom. -/
theorem fromPresheafValHom_comp_inv
    (F G : ringedSiteModuleCategory J O) :
    fromPresheafValHom O F G ≫ fromPresheafValInv O F G = 𝟙 _ := sorry

/-- The explicit inverse and forward internal-Hom maps compose to the identity on the canonical
internal Hom. -/
theorem fromPresheafValInv_comp_hom
    (F G : ringedSiteModuleCategory J O) :
    fromPresheafValInv O F G ≫ fromPresheafValHom O F G = 𝟙 _ := sorry

/-- If the source presheaf underlies a module sheaf, the sheafification-based internal Hom
canonically recovers `ihom`. -/
@[stacks 03EM "sheaf source"]
noncomputable def fromPresheafValIso
    (F G : ringedSiteModuleCategory J O) :
    fromPresheaf O F.val G ≅ (ihom F).obj G where
  hom := fromPresheafValHom O F G
  inv := fromPresheafValInv O F G
  hom_inv_id := fromPresheafValHom_comp_inv O F G
  inv_hom_id := fromPresheafValInv_comp_hom O F G

section Over

variable (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]

/-- The direct slice-site presentation inherits the canonical local-Hom closed structure.  This
bridge is the closed analogue of `ModuleOver.monoidalCategory`. -/
@[stacks 0E8H "canonical internal Hom on a slice site", instance_reducible]
noncomputable instance moduleOverMonoidalClosed :
    MonoidalClosed (SheafOfModules.{max u v} ((ringSheaf J O).over U)) :=
  moduleMonoidalClosed (J := J.over U) (O.over U)

/-- The canonical morphism comparing restriction of an internal Hom with the internal Hom of
the restrictions. -/
@[stacks 0E8H "slice comparison"]
noncomputable abbrev overComparison
    (F G : ringedSiteModuleCategory J O) :
    ((ihom F).obj G).over U ⟶ (ihom (F.over U)).obj (G.over U) :=
  CategoryTheory.Functor.LaxMonoidal.InternalHom.comparison
    (SheafOfModules.overFunctor (ringSheaf J O) U) F G

/-- The componentwise comparison isomorphism supplied by an internal-Hom preservation
hypothesis on restriction to the slice site. -/
@[stacks 0E8H "slice comparison isomorphism"]
noncomputable abbrev overComparisonIso
    (F G : ringedSiteModuleCategory J O)
    [IsIso (overComparison O U F G)] :
    ((ihom F).obj G).over U ≅ (ihom (F.over U)).obj (G.over U) :=
  CategoryTheory.Functor.LaxMonoidal.InternalHom.comparisonIso
    (SheafOfModules.overFunctor (ringSheaf J O) U) F G

/-- Under the internal-Hom preservation property, restriction to a slice commutes naturally
with internal Hom in the target module sheaf. -/
@[stacks 0E8H]
noncomputable abbrev overNatIso
    (F : ringedSiteModuleCategory J O)
    [CategoryTheory.Functor.LaxMonoidal.PreservesInternalHom
      (SheafOfModules.overFunctor (ringSheaf J O) U)] :
    ihom F ⋙ SheafOfModules.overFunctor (ringSheaf J O) U ≅
      SheafOfModules.overFunctor (ringSheaf J O) U ⋙ ihom (F.over U) :=
  CategoryTheory.Functor.LaxMonoidal.InternalHom.natIso
    (SheafOfModules.overFunctor (ringSheaf J O) U) F

end Over

end Closed



-- Both directions of the section/Hom equivalence are explicit objectwise constructions.  Any
-- `sorryAx` below comes from linearity, naturality, sheaf, or inverse laws, not hidden carrier or
-- morphism data.

-- The raw evaluation and currying functions below are explicit.  Any `sorryAx` in their bundled
-- linear, natural-transformation, or equivalence owners is confined to Prop-valued laws.

-- The chosen right adjoint in the following owners is `functor O F`; their `sorryAx` dependency
-- comes from naturality, inverse, and adjunction laws rather than hidden non-Prop witness data.

-- The only `sorryAx` in `overNatIso` comes from the Prop-valued naturality law of the generic
-- comparison; its objectwise isomorphisms are the explicit `overComparisonIso` components.

-- The morphism payload of `fromPresheafValIso` is given explicitly above.  Any `sorryAx`
-- reported for the bundled isomorphism is confined to its two equality proof fields.

end SheafOfModules.RingedSite.InternalHom
