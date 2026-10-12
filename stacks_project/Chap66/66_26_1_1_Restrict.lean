/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Unique
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Restriction of modules along étale morphisms of algebraic spaces

For an étale morphism `f : X ⟶ Y`, restriction of `𝒪_Y`-modules along the site functor
`j = etaleRestriction f` is the sheaf of modules `𝒢|_{X_étale}` with sections over `U` equal
to sections of `𝒢` over `jU`. A reducible postcomposition carrier supplies those sections
definitionally and is identified with `etaleRestriction` by `restrictPostcomposeIso`.
Restriction is isomorphic to module pullback `f^*` and, on underlying sheaves, to
`etaleRestrictionSheaf` and hence to `f_small⁻¹`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.Sheaf.InternalModule RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition of an étale morphism from a scheme with an étale morphism of algebraic
spaces remains étale. -/
instance etale_comp_hom (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    Etale (U.hom ≫ f) :=
  @Etale.etale_comp S _ X U.hom Y f U.prop ‹_›

/-- Reducible postcomposition carrier of `etaleRestriction`, sending `φ : U ⟶ X` to
`φ ≫ f : U ⟶ Y` with definitional `.left`. -/
def restrictPostcompose (f : X ⟶ Y) [Etale f] :
    smallEtaleSite X ⥤ smallEtaleSite Y where
  obj U := MorphismProperty.CostructuredArrow.mk ⊤ (U.hom ≫ f) (etale_comp_hom f U)
  map {_ _} h := MorphismProperty.CostructuredArrow.homMk h.left trivial sorry
  map_id := sorry
  map_comp := sorry

/-- On objects, `restrictPostcompose f` postcomposes the structure morphism with `f`. -/
@[simp]
theorem restrictPostcompose_obj (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    (restrictPostcompose f).obj U =
      MorphismProperty.CostructuredArrow.mk ⊤ (U.hom ≫ f) (etale_comp_hom f U) :=
  rfl

/-- Postcomposition with `f` does not change the underlying object of `Over S`. -/
@[simp]
theorem restrictPostcompose_obj_left (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    ((restrictPostcompose f).obj U).left = U.left :=
  rfl

/-- The reducible postcomposition carrier is continuous for the small étale topologies. -/
instance restrictPostcompose_isContinuous (f : X ⟶ Y) [Etale f] :
    (restrictPostcompose f).IsContinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  sorry

/-- The reducible postcomposition carrier is cocontinuous for the small étale topologies. -/
instance restrictPostcompose_isCocontinuous (f : X ⟶ Y) [Etale f] :
    (restrictPostcompose f).IsCocontinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  sorry

/-- Identity-on-left comparison from the reducible postcomposition carrier to
`etaleRestriction`. Components are `CostructuredArrow.homMk` of `𝟙`. -/
def restrictPostcomposeIso (f : X ⟶ Y) [Etale f] :
    restrictPostcompose f ≅ etaleRestriction f :=
  NatIso.ofComponents
    (fun _ ↦
      { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
        inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The forward component of `restrictPostcomposeIso` retains the identity on underlying
schemes over `S`. -/
@[simp]
theorem restrictPostcomposeIso_hom_app_left (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    ((restrictPostcomposeIso f).hom.app U).left = 𝟙 _ :=
  rfl

/-- The identity-on-sections comparison `𝒪_X ⟶ j_small⁻¹ 𝒪_Y` for an étale morphism
`f : X ⟶ Y`. -/
def restrictStructureMap (f : X ⟶ Y) [Etale f] :
    structureSheaf X ⟶
      ((restrictPostcompose f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (smallEtaleTopology Y)).obj (structureSheaf Y) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- The structure comparison of étale restriction is the identity on sections. -/
@[simp]
theorem restrictStructureMap_app (f : X ⟶ Y) [Etale f] (U : (smallEtaleSite X)ᵒᵖ) :
    (restrictStructureMap f).hom.app U = 𝟙 _ :=
  rfl

/-- Inverse of `restrictStructureMap`: identity on sections. -/
def restrictStructureMapInv (f : X ⟶ Y) [Etale f] :
    ((restrictPostcompose f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (smallEtaleTopology Y)).obj (structureSheaf Y) ⟶
      structureSheaf X :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- The two identity-on-sections comparisons compose to the identity of `𝒪_X`. -/
theorem restrictStructureMap_hom_inv_id (f : X ⟶ Y) [Etale f] :
    restrictStructureMap f ≫ restrictStructureMapInv f = 𝟙 (structureSheaf X) :=
  sorry

/-- The two identity-on-sections comparisons compose to the identity of `j_small⁻¹ 𝒪_Y`. -/
theorem restrictStructureMap_inv_hom_id (f : X ⟶ Y) [Etale f] :
    restrictStructureMapInv f ≫ restrictStructureMap f =
      𝟙 (((restrictPostcompose f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (smallEtaleTopology Y)).obj (structureSheaf Y)) :=
  sorry

/-- The identification `j_small⁻¹ 𝒪_Y = 𝒪_X` as sheaves of rings, given by identity on
sections. -/
def restrictStructureIso (f : X ⟶ Y) [Etale f] :
    structureSheaf X ≅
      ((restrictPostcompose f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (smallEtaleTopology Y)).obj (structureSheaf Y) where
  hom := restrictStructureMap f
  inv := restrictStructureMapInv f
  hom_inv_id := restrictStructureMap_hom_inv_id f
  inv_hom_id := restrictStructureMap_inv_hom_id f

/-- Restriction of sheaves of modules along an étale morphism of algebraic spaces. This is
isomorphic to `pullback` (see `restrictFunctorIsoPullback`) but has better definitional
behaviour on sections. -/
def restrictFunctor (f : X ⟶ Y) [Etale f] : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pushforward (restrictStructureMap f)

/-- The restriction of a sheaf of modules along an étale morphism of algebraic spaces. -/
abbrev restrict (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] : X.Modules :=
  (restrictFunctor f).obj 𝒢

/-- Objectwise, étale restriction is evaluation of `restrictFunctor`. -/
theorem restrict_obj (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] :
    restrict 𝒢 f = (restrictFunctor f).obj 𝒢 :=
  rfl

/-- Objectwise, `restrictFunctor` evaluates to `restrict`. -/
theorem restrictFunctor_obj (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (restrictFunctor f).obj 𝒢 = restrict 𝒢 f :=
  rfl

/-- Sections of `restrict 𝒢 f` over `U` identify with sections of `𝒢` over `jU`. -/
def restrictAppIso (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    (restrict 𝒢 f).val.obj (op U) ≅ 𝒢.val.obj (op ((restrictPostcompose f).obj U)) :=
  Iso.refl _

/-- The morphism `jU ⟶ V` in `Y_étale` associated to an `f`-square. -/
def restrictPostcomposeHomOfSquare (f : X ⟶ Y) [Etale f] (sq : EtaleSquare f) :
    (restrictPostcompose f).obj sq.left ⟶ sq.right :=
  MorphismProperty.CostructuredArrow.homMk sq.map trivial sq.w.symm

/-- The underlying scheme morphism of `restrictPostcomposeHomOfSquare` is the square edge. -/
@[simp]
theorem restrictPostcomposeHomOfSquare_left (f : X ⟶ Y) [Etale f] (sq : EtaleSquare f) :
    (restrictPostcomposeHomOfSquare f sq).left = sq.map :=
  rfl

/-- The Ran diagram of an `X`-module at the fibre product `X ×_Y V`. -/
abbrev restrictAdjunctionRanDiagram (f : X ⟶ Y) [Etale f] (M : X.Modules)
    (V : smallEtaleSite Y) :
    StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⥤ Type u :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⋙
    ((ToInternal.underlying (structureSheaf X)).obj M).obj

/-- The Ran diagram of a module sheaf has a limit, as a pointwise right Kan extension along
the small étale inclusion. -/
instance restrictAdjunctionRanDiagram_hasLimit (f : X ⟶ Y) [Etale f] (M : X.Modules)
    (V : smallEtaleSite Y) : HasLimit (restrictAdjunctionRanDiagram f M V) :=
  smallEtaleInclusion_op_hasPointwiseRightKanExtension_type X
    (((ToInternal.underlying (structureSheaf X)).obj M).obj)
    (op ((etaleBaseChange f).obj V))

/-- The Ran diagram is precomposition of the underlying type-valued sheaf with the structured
arrow projection. -/
theorem restrictAdjunctionRanDiagram_eq (f : X ⟶ Y) [Etale f] (M : X.Modules)
    (V : smallEtaleSite Y) :
    restrictAdjunctionRanDiagram f M V =
      StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⋙
        ((ToInternal.underlying (structureSheaf X)).obj M).obj :=
  rfl

/-- The Type-level restriction map `𝒢(V) ⟶ 𝒢(jU)` of an étale square. -/
def restrictAdjunctionUnitConeπ₀ (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (V : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op)
    (x : 𝒢.val.obj (op V)) :
    𝒢.val.obj (op ((restrictPostcompose f).obj (etaleSquareOfArrow f V a).left)) :=
  (𝒢.val.presheaf.map
    (op (restrictPostcomposeHomOfSquare f (etaleSquareOfArrow f V a)))).hom x

/-- Reinterpret `𝒢(jU)` as a section of the restricted module over `U`. -/
def restrictAdjunctionUnitConeπ (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (V : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op) :
    ((ToInternal.underlying (structureSheaf Y)).obj 𝒢).obj.obj (op V) ⟶
      (restrictAdjunctionRanDiagram f (restrict 𝒢 f) V).obj a :=
  ↾fun x ↦
    (ToInternal.sectionEquiv (structureSheaf X) (restrict 𝒢 f) a.right).symm
      ((restrictAppIso 𝒢 f a.right.unop).inv.hom
        (restrictAdjunctionUnitConeπ₀ f 𝒢 V a
          (ToInternal.sectionEquiv (structureSheaf Y) 𝒢 (op V) x)))

/-- The cone of restriction maps `𝒢(V) ⟶ 𝒢(jU)` presenting the unit at `V`. -/
def restrictAdjunctionUnitCone (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (V : smallEtaleSite Y) : Cone (restrictAdjunctionRanDiagram f (restrict 𝒢 f) V) where
  pt := ((ToInternal.underlying (structureSheaf Y)).obj 𝒢).obj.obj (op V)
  π :=
    { app := fun a ↦ restrictAdjunctionUnitConeπ f 𝒢 V a
      naturality := fun _ _ _ ↦ sorry }

/-- The graph morphism `U ⟶ X ×_Y jU` of a scheme étale over `X`. -/
def restrictGraph (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    ofOver U.left ⟶ etaleBaseChangeSpace f ((restrictPostcompose f).obj U) :=
  pullback.lift (f := homFunctor f)
    (g := homFunctor ((restrictPostcompose f).obj U).hom)
    (U.hom : (ofOver U.left).functorOfPoints ⟶ X.functorOfPoints)
    (𝟙 (ofOver U.left).functorOfPoints) rfl

/-- The first projection of `restrictGraph` is the structure morphism of `U`. -/
theorem restrictGraph_fst (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    restrictGraph f U ≫ etaleBaseChangeHom f ((restrictPostcompose f).obj U) = U.hom :=
  pullback.lift_fst (f := homFunctor f)
    (g := homFunctor ((restrictPostcompose f).obj U).hom) _ _ _

/-- The graph of `U` as a morphism over `X` in the spaces étale site. -/
def restrictGraphOver (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    (smallEtaleInclusion X).obj U ⟶
      (etaleBaseChange f).obj ((restrictPostcompose f).obj U) :=
  MorphismProperty.Over.homMk (restrictGraph f U) (restrictGraph_fst f U)

/-- The graph of `U` as a structured arrow for the Ran diagram at `X ×_Y jU`. -/
def restrictGraphArrow (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    StructuredArrow (op ((etaleBaseChange f).obj ((restrictPostcompose f).obj U)))
      (smallEtaleInclusion X).op :=
  StructuredArrow.mk (op (restrictGraphOver f U))

/-- Restrict the cone of actual étale-square section maps to the explicit small chart family. -/
def restrictAdjunctionSmallCone (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
      (SpacesEtale.AtlasCharts.inclusion X).op ⋙
      ((EtaleTopos.smallEquivalence X).functor.obj
        ((ToInternal.underlying (structureSheaf X)).obj (restrict 𝒢 f))).obj) where
  pt := ((ToInternal.underlying (structureSheaf Y)).obj 𝒢).obj.obj (op V)
  π :=
    { app := fun a ↦ restrictAdjunctionUnitConeπ f 𝒢 V
        (StructuredArrow.mk (Y := op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)) a.hom)
      naturality := sorry }

/-- The Type-level unit component `𝒢(V) ⟶ f_*(𝒢|_{X_étale})(V)`. -/
def restrictAdjunctionUnitAppType (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    ((ToInternal.underlying (structureSheaf Y)).obj 𝒢).obj.obj V ⟶
      ((ToInternal.underlying (structureSheaf Y)).obj
          ((pushforward f).obj ((restrictFunctor f).obj 𝒢))).obj.obj V :=
  (limit.lift _ (restrictAdjunctionSmallCone f 𝒢 V.unop) ≫
      ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj
          ((ToInternal.underlying (structureSheaf X)).obj (restrict 𝒢 f))).obj
        (op ((etaleBaseChange f).obj V.unop))).inv) ≫
    ((ModulePushforward.forgetIso (ringedToposHom f)).inv.app
      ((restrictFunctor f).obj 𝒢)).hom.app V

/-- The underlying type-valued sheaf map of the restriction–pushforward unit. -/
def restrictAdjunctionUnitUnderlying (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (ToInternal.underlying (structureSheaf Y)).obj 𝒢 ⟶
      (ToInternal.underlying (structureSheaf Y)).obj
        ((pushforward f).obj ((restrictFunctor f).obj 𝒢)) :=
  InducedCategory.homMk
    { app := fun V ↦ restrictAdjunctionUnitAppType f 𝒢 V
      naturality := fun _ _ _ ↦ sorry }

/-- The unit component `𝒢 ⟶ f_*(𝒢|_{X_étale})` as a morphism of sheaves of modules. -/
def restrictAdjunctionUnitApp (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    𝒢 ⟶ (pushforward f).obj ((restrictFunctor f).obj 𝒢) :=
  homOfUnderlying (structureSheaf Y) (restrictAdjunctionUnitUnderlying f 𝒢) sorry sorry

/-- The unit of étale restriction ⊣ module pushforward. -/
def restrictAdjunctionUnit (f : X ⟶ Y) [Etale f] :
    𝟭 Y.Modules ⟶ restrictFunctor f ⋙ pushforward f where
  app := restrictAdjunctionUnitApp f
  naturality := sorry

/-- The Type-level counit component `f_*(M)(jU) ⟶ M(U)`. -/
def restrictAdjunctionCounitAppType (f : X ⟶ Y) [Etale f] (M : X.Modules)
    (U : smallEtaleSite X) :
    ((ToInternal.underlying (structureSheaf X)).obj
        ((restrictFunctor f).obj ((pushforward f).obj M))).obj.obj (op U) ⟶
      ((ToInternal.underlying (structureSheaf X)).obj M).obj.obj (op U) :=
  ((ModulePushforward.forgetIso (ringedToposHom f)).hom.app M).hom.app
      (op ((restrictPostcompose f).obj U)) ≫
    EtaleTopos.extensionEvaluation X ((ToInternal.underlying (structureSheaf X)).obj M)
      (restrictGraphOver f U)

/-- The underlying type-valued sheaf map of the restriction–pushforward counit. -/
def restrictAdjunctionCounitUnderlying (f : X ⟶ Y) [Etale f] (M : X.Modules) :
    (ToInternal.underlying (structureSheaf X)).obj
        ((restrictFunctor f).obj ((pushforward f).obj M)) ⟶
      (ToInternal.underlying (structureSheaf X)).obj M :=
  InducedCategory.homMk
    { app := fun U ↦ restrictAdjunctionCounitAppType f M U.unop
      naturality := fun _ _ _ ↦ sorry }

/-- The counit component ` (f_* M)|_{X_étale} ⟶ M` as a morphism of sheaves of modules. -/
def restrictAdjunctionCounitApp (f : X ⟶ Y) [Etale f] (M : X.Modules) :
    (restrictFunctor f).obj ((pushforward f).obj M) ⟶ M :=
  homOfUnderlying (structureSheaf X) (restrictAdjunctionCounitUnderlying f M) sorry sorry

/-- The counit of étale restriction ⊣ module pushforward. -/
def restrictAdjunctionCounit (f : X ⟶ Y) [Etale f] :
    pushforward f ⋙ restrictFunctor f ⟶ 𝟭 X.Modules where
  app := restrictAdjunctionCounitApp f
  naturality := sorry

/-- The adjunction `restrictFunctor f ⊣ pushforward f` for an étale morphism of algebraic
spaces, with unit and counit given by the canonical sectionwise comparison maps. -/
def restrictAdjunction (f : X ⟶ Y) [Etale f] :
    restrictFunctor f ⊣ pushforward f :=
  Adjunction.mkOfUnitCounit
    { unit := restrictAdjunctionUnit f
      counit := restrictAdjunctionCounit f
      left_triangle := sorry
      right_triangle := sorry }

/-- Étale restriction of modules is left adjoint to module pushforward. -/
instance restrictFunctor_isLeftAdjoint (f : X ⟶ Y) [Etale f] :
    (restrictFunctor f).IsLeftAdjoint :=
  (restrictAdjunction f).isLeftAdjoint

/-- The unit of `restrictAdjunction` is `restrictAdjunctionUnit`. -/
theorem restrictAdjunction_unit (f : X ⟶ Y) [Etale f] :
    (restrictAdjunction f).unit = restrictAdjunctionUnit f :=
  rfl

/-- The component of the restriction–pushforward unit at `𝒢` is `restrictAdjunctionUnitApp`. -/
theorem restrictAdjunction_unit_app (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (restrictAdjunction f).unit.app 𝒢 = restrictAdjunctionUnitApp f 𝒢 :=
  rfl

/-- The counit of `restrictAdjunction` is `restrictAdjunctionCounit`. -/
theorem restrictAdjunction_counit (f : X ⟶ Y) [Etale f] :
    (restrictAdjunction f).counit = restrictAdjunctionCounit f :=
  rfl

/-- The component of the restriction–pushforward counit at `M` is `restrictAdjunctionCounitApp`. -/
theorem restrictAdjunction_counit_app (f : X ⟶ Y) [Etale f] (M : X.Modules) :
    (restrictAdjunction f).counit.app M = restrictAdjunctionCounitApp f M :=
  rfl

/-- The unit of `restrictAdjunction` at `𝒢` is adjoint transpose of the identity of
`restrict 𝒢 f`. -/
theorem restrictAdjunction_homEquiv_id (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (restrictAdjunction f).homEquiv 𝒢 ((restrictFunctor f).obj 𝒢) (𝟙 _) =
      (restrictAdjunction f).unit.app 𝒢 :=
  sorry

/-- The identification `𝒢 |_{X_étale} = f^* 𝒢` as functors on sheaves of modules, obtained
from uniqueness of left adjoints to `pushforward`. -/
def restrictFunctorIsoPullback (f : X ⟶ Y) [Etale f] :
    restrictFunctor f ≅ pullback f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

/-- Objectwise, étale restriction is isomorphic to module pullback. -/
abbrev restrictIsoPullback (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] :
    restrict 𝒢 f ≅ (pullback f).obj 𝒢 :=
  (restrictFunctorIsoPullback f).app 𝒢

/-- The component of `restrictFunctorIsoPullback` at a module sheaf is `restrictIsoPullback`. -/
theorem restrictFunctorIsoPullback_app (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] :
    (restrictFunctorIsoPullback f).app 𝒢 = restrictIsoPullback 𝒢 f :=
  rfl

/-- Compatibility of units characterizing `restrictFunctorIsoPullback`. -/
theorem restrictFunctorIsoPullback_spec (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (restrictAdjunction f).unit.app 𝒢 ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).hom.app 𝒢) =
      (pullbackPushforwardAdjunction f).unit.app 𝒢 :=
  sorry

/-- The underlying type-valued sheaf of étale module restriction is sheaf restriction along
the reducible postcomposition carrier. -/
def restrictUnderlyingIsoPostcompose (f : X ⟶ Y) [Etale f] :
    restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
      ToInternal.underlying (structureSheaf Y) ⋙
        (restrictPostcompose f).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology X) (smallEtaleTopology Y) :=
  NatIso.ofComponents
    (fun _ ↦
      { hom := ⟨{ app := fun _ ↦ 𝟙 _
                  naturality := fun _ _ _ ↦ sorry }⟩
        inv := ⟨{ app := fun _ ↦ 𝟙 _
                  naturality := fun _ _ _ ↦ sorry }⟩
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The identification `𝒢|_{X_étale} = f_small⁻¹ 𝒢` on underlying sheaves: restriction of
modules, forgotten to types, is sheaf restriction along `etaleRestriction`. Compose with
`etaleRestrictionSheaf_iso_inverseImage` to reach cocontinuous inverse image. The `𝒪_X`-action
is the identity-on-sections comparison `restrictStructureIso`. -/
def restrictFunctorIsoInverseImage (f : X ⟶ Y) [Etale f] :
    restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
      ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u) :=
  restrictUnderlyingIsoPostcompose f ≪≫
    Functor.isoWhiskerLeft (ToInternal.underlying (structureSheaf Y))
      (Functor.sheafPushforwardContinuousIso (restrictPostcomposeIso f) (Type u)
        (smallEtaleTopology X) (smallEtaleTopology Y))

/-- Objectwise, the underlying sheaf of étale module restriction is étale sheaf restriction. -/
abbrev restrictIsoInverseImage (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] :
    (ToInternal.underlying (structureSheaf X)).obj (restrict 𝒢 f) ≅
      (etaleRestrictionSheaf f (Type u)).obj
        ((ToInternal.underlying (structureSheaf Y)).obj 𝒢) :=
  (restrictFunctorIsoInverseImage f).app 𝒢

/-- The component of `restrictFunctorIsoInverseImage` at a module sheaf is
`restrictIsoInverseImage`. -/
theorem restrictFunctorIsoInverseImage_app (𝒢 : Y.Modules) (f : X ⟶ Y) [Etale f] :
    (restrictFunctorIsoInverseImage f).app 𝒢 = restrictIsoInverseImage 𝒢 f :=
  rfl

/-- Inverse-image comparison is restriction of scalars along `restrictStructureIso` on
underlying sections. -/
theorem restrictFunctorIsoInverseImage_spec (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules)
    (U : smallEtaleSite X) :
    ((restrictFunctorIsoInverseImage f).hom.app 𝒢).hom.app (op U) =
      ((ToInternal.underlying (structureSheaf Y)).obj 𝒢).obj.map
        (op ((restrictPostcomposeIso f).hom.app U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
