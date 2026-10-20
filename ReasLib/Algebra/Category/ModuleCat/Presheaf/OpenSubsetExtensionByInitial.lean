module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.Topology.Presheaf.ExtensionByInitial.Properties
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PushforwardAdjunction
public import ReasLib.Topology.Sheaves.Ring.Definition

/-!
# Extension by zero for presheaves of modules on open subspaces

This module owns the module-presheaf specialization of extension by an initial object along an
open subspace inclusion. The coefficient-category-generic construction and its presheaf
adjunction are owned by `TopCat.Presheaf.ExtensionByInitial`; sheafification and the sheaf-level
adjunction live in the corresponding `TopCat.Sheaf.ExtensionByInitial` owner.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens
open CategoryTheory.Limits
open TopCat.Opens.Subspace
open scoped ZeroObject

noncomputable section

universe u w

section Modules

variable {X : TopCat.{u}}

namespace PresheafOfModules.OpenSubset.ExtensionByZero

/-- The chosen initial object of `AddCommGrpCat` has a subsingleton carrier. -/
-- Local instance justification (instance diamond): keep the initial-object carrier fact scoped
-- to the extension construction instead of competing globally with zero-object instances.
local instance instSubsingletonInitialAddCommGrpCat :
    Subsingleton (⊥_ AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero initialIsInitial.isZero

/-- The chosen zero object of `AddCommGrpCat` has a subsingleton carrier. -/
-- Local instance justification (instance diamond): keep the zero-object carrier fact scoped to
-- the extension construction instead of competing globally with initial-object instances.
local instance instSubsingletonZeroAddCommGrpCat :
    Subsingleton (0 : AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero (isZero_zero _)

/-- The objectwise ambient-ring module structure on additive extension by zero, obtained by
restriction of scalars on opens contained in `U` and by the unique action on the zero object
otherwise. -/
@[reducible] noncomputable def moduleStructure
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) (V : (Opens X)ᵒᵖ) :
    Module (𝒪X.obj V) (((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).obj V) := by
  classical
  by_cases hV : V.unop ≤ U
  · let αV : 𝒪X.obj V ⟶ 𝒪U.obj (op (TopCat.Opens.Subspace.preimageOpen U V.unop)) := by
      simpa using α.app V
    -- Local instance justification (defeq pin): the returned action must use restriction of
    -- scalars along the component `αV` on this exact preimage open.
    letI : Module (𝒪X.obj V) (ℱ.presheaf.obj (op (TopCat.Opens.Subspace.preimageOpen U V.unop))) :=
      Module.compHom (ℱ.presheaf.obj (op (TopCat.Opens.Subspace.preimageOpen U V.unop))) αV.hom
    change Module (𝒪X.obj V)
      (TopCat.Presheaf.ExtensionByInitial.value (C := AddCommGrpCat.{u}) U ℱ.presheaf V)
    rw [TopCat.Presheaf.ExtensionByInitial.value_eq_of_le (C := AddCommGrpCat.{u}) U ℱ.presheaf hV]
    infer_instance
  · change Module (𝒪X.obj V)
      (TopCat.Presheaf.ExtensionByInitial.value (C := AddCommGrpCat.{u}) U ℱ.presheaf V)
    rw [TopCat.Presheaf.ExtensionByInitial.value_eq_of_not_le (C := AddCommGrpCat.{u}) U ℱ.presheaf hV]
    exact
      { smul := fun _ _ ↦ 0
        one_smul := fun _ ↦ Subsingleton.elim _ _
        mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        smul_zero := fun _ ↦ Subsingleton.elim _ _
        smul_add := fun _ _ _ ↦ Subsingleton.elim _ _
        add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        zero_smul := fun _ ↦ Subsingleton.elim _ _ }

end PresheafOfModules.OpenSubset.ExtensionByZero

namespace PresheafOfModules.OpenSubset.ExtensionByZero
/-- Outside the open subspace, the additive extension restriction map is zero. -/
private theorem presheafMap_eq_zero_of_not_le
    (U : Opens X) (ℱ : (TopCat.Opens.Subspace.space U).Presheaf AddCommGrpCat.{u})
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : ¬ V.unop ≤ U) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ).map i = 0 := sorry

/-- Restriction maps of the extended module presheaf are semilinear on opens contained in `U`. -/
private theorem presheafMap_smul_of_le
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : V.unop ≤ U)
    (hW : W.unop ≤ U) (r : 𝒪X.obj V)
    (m : ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).obj V) :
    -- Local instance justification (defeq pin): semilinearity compares the two explicitly
    -- transported module actions selected by `moduleStructure`.
    letI := PresheafOfModules.OpenSubset.ExtensionByZero.moduleStructure U α ℱ V
    -- Local instance justification (defeq pin): the target action must be the corresponding
    -- transported action on `W`.
    letI := PresheafOfModules.OpenSubset.ExtensionByZero.moduleStructure U α ℱ W
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).map i (r • m) =
      (𝒪X.map i) r • ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).map i m := sorry

/-- The presheaf of ambient-ring modules obtained by extending a module presheaf by zero along
the open inclusion and restricting scalars through `α`. -/
noncomputable def obj
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) :
    PresheafOfModules.{u} 𝒪X :=
  -- Local instance justification (defeq pin): `ofPresheaf` must use the objectwise actions
  -- constructed by `moduleStructure` as its definitional module instances.
  letI : ∀ V : (Opens X)ᵒᵖ,
      Module (𝒪X.obj V) (((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).obj V) :=
    fun V ↦ PresheafOfModules.OpenSubset.ExtensionByZero.moduleStructure U α ℱ V
  PresheafOfModules.ofPresheaf
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf)
    (by
      intro V W i r m
      classical
      by_cases hV : V.unop ≤ U
      · have hW : W.unop ≤ U := le_trans i.unop.le hV
        -- Inside `U`, semilinearity is the dedicated scalar-transport lemma above.
        exact presheafMap_smul_of_le U α ℱ i hV hW r m
      · -- Outside `U`, the restriction map is zero, so both sides reduce by `map_zero` and
        -- `smul_zero`.
        rw [presheafMap_eq_zero_of_not_le U ℱ.presheaf i hV]
        simp)

/-- The component over an ambient open of the module extension-by-zero map. -/
noncomputable def mapApp
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).obj V ⟶
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj 𝒢.presheaf).obj V :=
  TopCat.Presheaf.ExtensionByInitial.homApp U
    ((PresheafOfModules.toPresheaf _).map η) V

/-- Forgetting the module structure, `mapApp` is the canonical
extension-by-initial component. -/
@[simp]
theorem mapApp_eq
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) :
    mapApp U η V =
      TopCat.Presheaf.ExtensionByInitial.homApp U
        ((PresheafOfModules.toPresheaf _).map η) V := sorry

/-- Each component of the module extension-by-zero map is linear for the transported action. -/
private theorem mapApp_smul
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) (r : 𝒪X.obj V)
    (m : ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).obj V) :
    -- Local instance justification (defeq pin): linearity uses the source action selected by
    -- `moduleStructure` on the fixed open `V`.
    letI := PresheafOfModules.OpenSubset.ExtensionByZero.moduleStructure U α ℱ V
    -- Local instance justification (defeq pin): linearity uses the target action selected by
    -- `moduleStructure` on the same fixed open `V`.
    letI := PresheafOfModules.OpenSubset.ExtensionByZero.moduleStructure U α 𝒢 V
    mapApp U η V (r • m) =
      r • mapApp U η V m := sorry

/-- Components of a module extension-by-zero map commute with ambient restrictions. -/
theorem mapApp_naturality
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf).map i ≫
        mapApp U η W =
      mapApp U η V ≫
        ((TopCat.Presheaf.ExtensionByInitial.functor U).obj 𝒢.presheaf).map i := sorry

/-- The morphism of ambient module presheaves obtained by extending a source morphism by zero. -/
noncomputable def map
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) :
    obj U α ℱ ⟶
      obj U α 𝒢 :=
  set_option backward.isDefEq.respectTransparency false in
    PresheafOfModules.homMk
      { app := mapApp U η
        naturality := fun {_ _} i ↦ mapApp_naturality U η i }
      (fun V r m ↦ by
        exact mapApp_smul U α η V r m)

/-- After forgetting the module structure, an extension-by-zero morphism is the
presheaf-level extension-by-initial-object morphism on the underlying additive presheaves. -/
@[simp]
theorem map_toPresheaf_eq
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) :
    (PresheafOfModules.toPresheaf 𝒪X).map (map U α η) =
    TopCat.Presheaf.ExtensionByInitial.hom U ((PresheafOfModules.toPresheaf _).map η) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Extending the identity morphism by zero gives the identity on the extended module
presheaf. -/
theorem map_id
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) :
    map U α (𝟙 ℱ) =
      𝟙 (obj U α ℱ) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero respects composition of module-presheaf morphisms. -/
theorem map_comp
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    {ℱ 𝒢 ℋ : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    map U α (η ≫ θ) =
      map U α η ≫
        map U α θ := sorry

end PresheafOfModules.OpenSubset.ExtensionByZero

namespace PresheafOfModules.OpenSubset.ExtensionByZero

/-- Forgetting `obj U α ℱ` recovers the canonical additive extension-by-initial presheaf. -/
@[simp]
theorem obj_presheaf
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) :
    (obj U α ℱ).presheaf =
      (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf := sorry

/-- Extension by zero for module presheaves relative to a ring-presheaf map into the
open-subset pushforward. -/
noncomputable def functor
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U) :
    PresheafOfModules.{u} 𝒪U ⥤ PresheafOfModules.{u} 𝒪X where
  obj := obj U α
  map := fun η ↦ map U α η
  map_id := map_id U α
  map_comp := map_comp U α

/-- The object of the extension-by-zero functor is `obj`. -/
@[simp]
theorem functor_obj
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules.{u} 𝒪U) :
    (functor U α).obj ℱ = obj U α ℱ := sorry

/-- The map of the extension-by-zero functor is `map`. -/
@[simp]
theorem functor_map
    (U : Opens X) {𝒪U : (TopCat.Opens.Subspace.space U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules.{u} 𝒪U} (η : ℱ ⟶ 𝒢) :
    (functor U α).map η = map U α η := sorry

/-- Extension by zero along the canonical pullback-pushforward unit for a ring presheaf. -/
noncomputable abbrev functorOfPullback
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{u}) :
    PresheafOfModules ((TopCat.Presheaf.pullback RingCat (TopCat.Opens.Subspace.inclusion U)).obj 𝒪) ⥤
      PresheafOfModules 𝒪 :=
  functor U
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
      (TopCat.Opens.Subspace.inclusion U)).unit.app 𝒪)

end PresheafOfModules.OpenSubset.ExtensionByZero

end Modules

section ModuleAdjunction

variable {X : TopCat.{w}}

namespace PresheafOfModules.OpenSubset.ExtensionByZero

/-- A pair of coefficient-ring maps for an open subspace inclusion that are mates for the
open-image/open-preimage adjunction.  This is the coefficient data needed to identify
extension by zero with the left adjoint of restriction on module presheaves. -/
@[ext]
structure RingMapMate
    (U : Opens X) (𝒪X : X.Presheaf RingCat.{w})
    (𝒪U : (space U).Presheaf RingCat.{w}) where
  /-- The ambient coefficient map into the open-subset pushforward. -/
  toPushforward :
    𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (inclusion U)).obj 𝒪U
  /-- The subspace coefficient map into the pullback of the ambient coefficients. -/
  toPullback : 𝒪U ⟶ U.isOpenEmbedding.functor.op ⋙ 𝒪X
  /-- The counit-side mate identity. -/
  counit_eq :
    Functor.whiskerRight
        (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) 𝒪X =
      toPushforward ≫ (Opens.map (inclusion U)).op.whiskerLeft toPullback
  /-- The unit-side mate identity. -/
  unit_eq :
    toPullback ≫ U.isOpenEmbedding.functor.op.whiskerLeft toPushforward ≫
        Functor.whiskerRight
          (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit) 𝒪U =
      𝟙 𝒪U

namespace RingMapMate

variable {U : Opens X} {𝒪U : (space U).Presheaf RingCat.{w}}
  {𝒪X : X.Presheaf RingCat.{w}}

/-- The objectwise additive map of the transpose associated to a coefficient-ring mate. -/
noncomputable def toRestrictionApp
    (m : RingMapMate U 𝒪X 𝒪U)
    {ℱ : PresheafOfModules 𝒪U} {𝒢 : PresheafOfModules 𝒪X}
    (η : (functor U m.toPushforward).obj ℱ ⟶ 𝒢) (V : (Opens (space U))ᵒᵖ) :
    ℱ.presheaf.obj V ⟶
      ((PresheafOfModules.pushforward m.toPullback).obj 𝒢).presheaf.obj V :=
  TopCat.Presheaf.ExtensionByInitial.Properties.unitApp U ℱ.presheaf V ≫
    ((TopCat.Presheaf.pullback AddCommGrpCat (inclusion U)).map
        ((PresheafOfModules.toPresheaf 𝒪X).map η)).app V ≫
    (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒢.presheaf).hom.app V

/-- Transpose a morphism out of extension by zero using a coefficient-ring mate. -/
noncomputable def toRestriction
    (m : RingMapMate U 𝒪X 𝒪U)
    {ℱ : PresheafOfModules 𝒪U} {𝒢 : PresheafOfModules 𝒪X}
    (η : (functor U m.toPushforward).obj ℱ ⟶ 𝒢) :
    ℱ ⟶ (PresheafOfModules.pushforward m.toPullback).obj 𝒢 :=
  PresheafOfModules.homMk
    { app := toRestrictionApp m η
      naturality := sorry }
    sorry

/-- The objectwise additive map of the inverse transpose associated to a coefficient-ring
mate. -/
noncomputable def liftApp
    (m : RingMapMate U 𝒪X 𝒪U)
    {ℱ : PresheafOfModules 𝒪U} {𝒢 : PresheafOfModules 𝒪X}
    (η : ℱ ⟶ (PresheafOfModules.pushforward m.toPullback).obj 𝒢) (V : (Opens X)ᵒᵖ) :
    ((functor U m.toPushforward).obj ℱ).presheaf.obj V ⟶ 𝒢.presheaf.obj V :=
  TopCat.Presheaf.ExtensionByInitial.Properties.liftApp U
    ((PresheafOfModules.toPresheaf _).map η ≫
      (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒢.presheaf).inv) V

/-- Invert the transpose associated to a coefficient-ring mate. -/
noncomputable def lift
    (m : RingMapMate U 𝒪X 𝒪U)
    {ℱ : PresheafOfModules 𝒪U} {𝒢 : PresheafOfModules 𝒪X}
    (η : ℱ ⟶ (PresheafOfModules.pushforward m.toPullback).obj 𝒢) :
    (functor U m.toPushforward).obj ℱ ⟶ 𝒢 :=
  PresheafOfModules.homMk
    { app := liftApp m η
      naturality := sorry }
    sorry

/-- The bifunctorial Hom equivalence induced by a coefficient-ring mate. -/
noncomputable def homEquiv
    (m : RingMapMate U 𝒪X 𝒪U) (ℱ : PresheafOfModules 𝒪U)
    (𝒢 : PresheafOfModules 𝒪X) :
    ((functor U m.toPushforward).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (PresheafOfModules.pushforward m.toPullback).obj 𝒢) :=
  { toFun := toRestriction m
    invFun := lift m
    left_inv := sorry
    right_inv := sorry }

/-- Extension by zero is left adjoint to restriction for a coefficient-ring mate. -/
noncomputable def adjunction (m : RingMapMate U 𝒪X 𝒪U) :
    functor U m.toPushforward ⊣ PresheafOfModules.pushforward m.toPullback :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv m
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Restriction of scalars along a coefficient-ring mate is left adjoint to direct image along
its ambient coefficient map. -/
noncomputable def restrictionPushforwardAdjunction (m : RingMapMate U 𝒪X 𝒪U) :
    PresheafOfModules.pushforward m.toPullback ⊣
      PresheafOfModules.pushforward m.toPushforward :=
  PresheafOfModules.pushforwardPushforwardAdj
    U.isOpenEmbedding.isOpenMap.adjunction
    m.toPullback m.toPushforward m.counit_eq m.unit_eq

end RingMapMate

/-- The explicit restriction of presheaves of modules to an open subspace, obtained by
precomposition with the ambient-image functor and restriction of scalars along the open-map
pullback comparison. -/
noncomputable def restriction
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    PresheafOfModules 𝒪 ⥤
      PresheafOfModules ((TopCat.Presheaf.pullback RingCat (inclusion U)).obj 𝒪) :=
  PresheafOfModules.pushforward
    (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪).hom

/-- The canonical presheaf pullback unit and the open-map pullback comparison satisfy the
counit-side mate identity for the adjunction on opens. -/
theorem pullbackRingMap_counit
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    Functor.whiskerRight
        (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) 𝒪 =
      (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪 ≫
        (Opens.map (inclusion U)).op.whiskerLeft
          (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪).hom := sorry

/-- The canonical presheaf pullback unit and the open-map pullback comparison satisfy the
unit-side mate identity for the adjunction on opens. -/
theorem pullbackRingMap_unit
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪).hom ≫
        U.isOpenEmbedding.functor.op.whiskerLeft
          ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
            (inclusion U)).unit.app 𝒪) ≫
        Functor.whiskerRight
          (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit)
          ((TopCat.Presheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪) =
      𝟙 ((TopCat.Presheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪) := sorry

/-- The canonical coefficient-ring mate for the pullback and pushforward along an open-subspace
inclusion. -/
noncomputable def pullbackRingMapMate
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    RingMapMate U 𝒪
      ((TopCat.Presheaf.pullback RingCat (inclusion U)).obj 𝒪) where
  toPushforward :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat (inclusion U)).unit.app 𝒪
  toPullback := (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪).hom
  counit_eq := pullbackRingMap_counit U 𝒪
  unit_eq := pullbackRingMap_unit U 𝒪

/-- The pushforward map of `pullbackRingMapMate U 𝒪` is the canonical presheaf pullback unit. -/
@[simp]
theorem pullbackRingMapMate_toPushforward
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    (pullbackRingMapMate U 𝒪).toPushforward =
      (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat (inclusion U)).unit.app 𝒪 := sorry

/-- The pullback map of `pullbackRingMapMate U 𝒪` is the open-map pullback comparison. -/
@[simp]
theorem pullbackRingMapMate_toPullback
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    (pullbackRingMapMate U 𝒪).toPullback =
      (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪).hom := sorry

/-- Transpose a morphism out of module-presheaf extension by zero to a morphism into the
explicit open-subspace restriction. -/
noncomputable def toRestriction
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w})
    {ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat (inclusion U)).obj 𝒪)}
    {𝒢 : PresheafOfModules 𝒪}
    (η : (functorOfPullback U 𝒪).obj ℱ ⟶ 𝒢) :
    ℱ ⟶ (restriction U 𝒪).obj 𝒢 :=
  RingMapMate.toRestriction (pullbackRingMapMate U 𝒪) η

/-- Transpose a morphism into the explicit open-subspace restriction to a morphism out of
module-presheaf extension by zero. -/
noncomputable def lift
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w})
    {ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat (inclusion U)).obj 𝒪)}
    {𝒢 : PresheafOfModules 𝒪}
    (η : ℱ ⟶ (restriction U 𝒪).obj 𝒢) :
    (functorOfPullback U 𝒪).obj ℱ ⟶ 𝒢 :=
  RingMapMate.lift (pullbackRingMapMate U 𝒪) η

/-- The bifunctorial Hom equivalence between module-presheaf extension by zero and the explicit
open-subspace restriction. -/
noncomputable def homEquiv
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w})
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat (inclusion U)).obj 𝒪))
    (𝒢 : PresheafOfModules 𝒪) :
    ((functorOfPullback U 𝒪).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (restriction U 𝒪).obj 𝒢) :=
  RingMapMate.homEquiv (pullbackRingMapMate U 𝒪) ℱ 𝒢

/-- Module-presheaf extension by zero is left adjoint to the explicit restriction model for an
open-subspace inclusion. -/
noncomputable def restrictionAdjunction
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    functorOfPullback U 𝒪 ⊣ restriction U 𝒪 :=
  RingMapMate.adjunction (pullbackRingMapMate U 𝒪)

/-- The explicit open-subspace restriction of module presheaves is left adjoint to the canonical
module direct-image functor. -/
noncomputable def restrictionPushforwardAdjunction
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    restriction U 𝒪 ⊣
      PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪) :=
  RingMapMate.restrictionPushforwardAdjunction (pullbackRingMapMate U 𝒪)

/-- The explicit open-subspace restriction model for module presheaves is canonically isomorphic
to mathlib's pullback owner. -/
noncomputable def restrictionIsoPullback
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    restriction U 𝒪 ≅
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪) :=
  Adjunction.leftAdjointUniq
    (restrictionPushforwardAdjunction U 𝒪)
    (PresheafOfModules.pullbackPushforwardAdjunction
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
        (inclusion U)).unit.app 𝒪))

/-! ### Commutative-ring coefficients -/

namespace CommRing

/-- Restriction of modules over a commutative-ring presheaf to an open subspace.

The scalar presheaf on the subspace is the underlying ring presheaf of the commutative-ring
pullback.  The coefficient comparison
`TopCat.Presheaf.ringPresheafOfCommPullbackIso` relates this scalar presheaf to the
`RingCat` pullback used by the generic explicit restriction model. -/
noncomputable abbrev restriction
    (U : Opens X) (𝒪 : X.Presheaf CommRingCat.{w}) :
    PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪) ⥤
      PresheafOfModules
        (CategoryTheory.Presheaf.ringPresheafOfComm
          ((TopCat.Presheaf.pullback CommRingCat (inclusion U)).obj 𝒪)) :=
  PresheafOfModules.pullback
    (TopCat.Presheaf.commRingPresheafPullbackUnit (inclusion U) 𝒪)

end CommRing

/-- Module-presheaf extension by zero is canonically left adjoint to mathlib's module restriction
functor along an open-subspace inclusion. -/
noncomputable def adjunction
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{w}) :
    functorOfPullback U 𝒪 ⊣
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪) :=
  (restrictionAdjunction U 𝒪).ofNatIsoRight
    (restrictionIsoPullback U 𝒪)

end PresheafOfModules.OpenSubset.ExtensionByZero

end ModuleAdjunction
