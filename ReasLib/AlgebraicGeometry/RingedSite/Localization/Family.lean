module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Ambient
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Sites.Family.Localization
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.DirectSum

/-!
# Ringed localization at a semi-representable family

The ringed site `(C / K, O_K)` with `O_K = j⁻¹ O_C` is built on the unringed site
`OverSite K`, together with the product decomposition of modules
and the morphisms of ringed topoi `j` and `f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.SemiRepresentableFamily

noncomputable section

universe ι u v w z

namespace RingedSite.Localization.AtSR

open SemiRepresentableFamily (OverSite overTopology overIncl overMap forget_comp_incl overMap_comp_incl)

variable {X : RingedSite.{u, v, w}}

/-- The structure sheaf `O_K = j⁻¹ O_C` of the localization of a ringed site at
`K : SR(C)`. -/
abbrev ringSheaf (K : Limits.FormalCoproduct.{ι} X.carrier) :
    Sheaf (overTopology X.siteTopology K) RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (SemiRepresentableFamily.forget K) X.structureSheaf

/-- The ringed site `(C / K, O_K)` obtained by localizing a ringed site at a
semi-representable family. -/
def site (K : Limits.FormalCoproduct.{ι} X.carrier) :
    RingedSite.{max ι u v, max ι u v, w} :=
  ofRingSheaf (overTopology X.siteTopology K) (ringSheaf K)

/-- The structure sheaf of `site K` is the continuous inverse image `j⁻¹ O_C`. -/
theorem structureSheaf_spec (K : Limits.FormalCoproduct.{ι} X.carrier) :
    (site K).structureSheaf = ringSheaf K :=
  rfl

/-- The comparison `incl^* O_K ≅ O.over (K.obj i)` induced by
`forget_comp_incl : overIncl i ⋙ forget K ≅ Over.forget (K.obj i)`. -/
def componentRingIso (K : Limits.FormalCoproduct.{ι} X.carrier) (i : K.I) :
    X.structureSheaf.over (K.obj i) ≅
      (@Functor.sheafPushforwardContinuous _ _ _ _ (overIncl K i) RingCat.{w} _
        (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K)
        (CategoryTheory.Sigma.incl_isContinuous
          (fun index : K.I ↦ X.siteTopology.over (K.obj index)) i)).obj (ringSheaf K) :=
  (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (forget_comp_incl K i) RingCat.{w} _
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K) X.siteTopology
    (CategoryTheory.Sigma.incl_isContinuous
      (fun index : K.I ↦ X.siteTopology.over (K.obj index)) i)
    inferInstance inferInstance).symm.app X.structureSheaf

/-- The coefficient map for component restriction is the identity on the
ring of sections at each slice object. -/
theorem componentRingIso_hom_app (K : Limits.FormalCoproduct.{ι} X.carrier)
    (i : K.I) (V : (Over (K.obj i))ᵒᵖ) :
    ((componentRingIso K i).hom.hom.app V).hom =
      RingHom.id (X.structureSheaf.obj.obj (op V.unop.left)) := sorry

/-- Restriction of modules on `(C / K, O_K)` to the slice summand `C / K.obj i`,
using `forget_comp_incl` as the coefficient map. -/
def component (K : Limits.FormalCoproduct.{ι} X.carrier) (i : K.I) :
    SheafOfModules.{z} (ringSheaf K) ⥤
      SheafOfModules.{z} (X.structureSheaf.over (K.obj i)) :=
  @SheafOfModules.pushforward _ _ _ _
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K) (overIncl K i) _ _
    (CategoryTheory.Sigma.incl_isContinuous
      (fun index : K.I ↦ X.siteTopology.over (K.obj index)) i)
    (componentRingIso K i).hom

/-- The product-decomposition functor `Mod(O_K) ⥤ ∏ᵢ Mod(O_{U_i})`. -/
def modulesEquivFunctor (K : Limits.FormalCoproduct.{ι} X.carrier) :
    SheafOfModules.{z} (ringSheaf K) ⥤
      ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)) where
  obj M i := (component K i).obj M
  map f i := (component K i).map f
  map_id := sorry
  map_comp := sorry

/-- The restriction map of a glued presheaf of modules along a morphism of `C / K`. -/
def glueHom (K : Limits.FormalCoproduct.{ι} X.carrier)
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) :
    ∀ {x y : OverSite K} (f : CategoryTheory.Sigma.SigmaHom y x),
      (F x.1).val.obj (op x.2) ⟶
        (_root_.ModuleCat.restrictScalars (((ringSheaf K).obj).map
          (Quiver.Hom.op (f : y ⟶ x))).hom).obj
          ((F y.1).val.obj (op y.2))
  | _, _, .mk g => (F _).val.map g.op

/-- Underlying presheaf of modules obtained by gluing an `I`-indexed family of
modules on the slice sites `C / K.obj i`. -/
def glueVal (K : Limits.FormalCoproduct.{ι} X.carrier)
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) :
    PresheafOfModules.{z} (ringSheaf K).obj where
  obj U := (F U.unop.1).val.obj (op U.unop.2)
  map {U V} f := glueHom K F (Quiver.Hom.unop f)
  map_id := sorry
  map_comp := sorry

/-- Glue an `I`-indexed family of modules on the slices `C / K.obj i` to a module on
`(C / K, O_K)`. -/
def glue (K : Limits.FormalCoproduct.{ι} X.carrier)
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) :
    SheafOfModules.{z} (ringSheaf K) where
  val := glueVal K F
  isSheaf := sorry

/-- A morphism of families of slice modules induces a morphism of the glued modules. -/
def glueMap (K : Limits.FormalCoproduct.{ι} X.carrier)
    {F G : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))}
    (f : F ⟶ G) : glue K F ⟶ glue K G where
  val :=
    { app := fun U ↦ (f U.unop.1).val.app (op U.unop.2)
      naturality := sorry }

/-- The inverse product-decomposition functor `∏ᵢ Mod(O_{U_i}) ⥤ Mod(O_K)`. -/
def modulesEquivInverse (K : Limits.FormalCoproduct.{ι} X.carrier) :
    (∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) ⥤
      SheafOfModules.{z} (ringSheaf K) where
  obj F := glue K F
  map f := glueMap K f
  map_id := sorry
  map_comp := sorry

/-- The identity-on-objects comparison from a module on `C / K` to the glue of its
slice restrictions. -/
def modulesUnitApp (K : Limits.FormalCoproduct.{ι} X.carrier)
    (M : SheafOfModules.{z} (ringSheaf K)) :
    M ⟶ (modulesEquivInverse K).obj ((modulesEquivFunctor K).obj M) where
  val :=
    { app := fun U ↦
        (_root_.ModuleCat.restrictScalarsId'App
          (((componentRingIso K U.unop.1).hom.hom.app (op U.unop.2)).hom)
          (componentRingIso_hom_app K U.unop.1 (op U.unop.2))
          (M.val.obj U)).inv
      naturality := sorry }

/-- The inverse identity-on-objects comparison from the glue of slice restrictions
back to a module on `C / K`. -/
def modulesUnitInvApp (K : Limits.FormalCoproduct.{ι} X.carrier)
    (M : SheafOfModules.{z} (ringSheaf K)) :
    (modulesEquivInverse K).obj ((modulesEquivFunctor K).obj M) ⟶ M where
  val :=
    { app := fun U ↦
        (_root_.ModuleCat.restrictScalarsId'App
          (((componentRingIso K U.unop.1).hom.hom.app (op U.unop.2)).hom)
          (componentRingIso_hom_app K U.unop.1 (op U.unop.2))
          (M.val.obj U)).hom
      naturality := sorry }

/-- The identity-on-objects comparison from a family of slice modules to the
restrictions of its glue. -/
def modulesCounitApp (K : Limits.FormalCoproduct.{ι} X.carrier)
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) :
    (modulesEquivFunctor K).obj ((modulesEquivInverse K).obj F) ⟶ F :=
  fun i ↦
    { val :=
        { app := fun Y ↦
            (_root_.ModuleCat.restrictScalarsId'App
              (((componentRingIso K i).hom.hom.app Y).hom)
              (componentRingIso_hom_app K i Y)
              ((F i).val.obj Y)).hom
          naturality := sorry } }

/-- The inverse identity-on-objects comparison from a family of slice modules to the
restrictions of its glue. -/
def modulesCounitInvApp (K : Limits.FormalCoproduct.{ι} X.carrier)
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i))) :
    F ⟶ (modulesEquivFunctor K).obj ((modulesEquivInverse K).obj F) :=
  fun i ↦
    { val :=
        { app := fun Y ↦
            (_root_.ModuleCat.restrictScalarsId'App
              (((componentRingIso K i).hom.hom.app Y).hom)
              (componentRingIso_hom_app K i Y)
              ((F i).val.obj Y)).inv
          naturality := sorry } }

/-- The decomposition `Mod(O_K) ≌ ∏ᵢ Mod(O_{U_i})` of modules on the localization
of a ringed site at `K = {U_i}`. -/
def modulesEquiv (K : Limits.FormalCoproduct.{ι} X.carrier) :
    SheafOfModules.{z} (ringSheaf K) ≌
      ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)) where
  functor := modulesEquivFunctor K
  inverse := modulesEquivInverse K
  unitIso := NatIso.ofComponents
    (fun M ↦
      { hom := modulesUnitApp K M
        inv := modulesUnitInvApp K M
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry
  counitIso := NatIso.ofComponents
    (fun F ↦
      { hom := modulesCounitApp K F
        inv := modulesCounitInvApp K F
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry
  functor_unitIso_comp := sorry

/-- Evaluation of the product decomposition on objects. -/
theorem modulesEquiv_functor_obj (K : Limits.FormalCoproduct.{ι} X.carrier)
    (M : SheafOfModules.{z} (ringSheaf K)) (i : K.I) :
    ((modulesEquiv K).functor.obj M) i = (component K i).obj M :=
  rfl

/-- Continuity of `j : C / K ⥤ C` on the packaged ringed site `site K`. -/
instance forget_isContinuous_site (K : Limits.FormalCoproduct.{ι} X.carrier) :
    (SemiRepresentableFamily.forget K).IsContinuous
      (site K).siteTopology X.siteTopology :=
  SemiRepresentableFamily.forget_isContinuous X.siteTopology K

/-- Cocontinuity of `j : C / K ⥤ C` on the packaged ringed site `site K`. -/
instance forget_isCocontinuous_site (K : Limits.FormalCoproduct.{ι} X.carrier) :
    (SemiRepresentableFamily.forget K).IsCocontinuous
      (site K).siteTopology X.siteTopology :=
  SemiRepresentableFamily.forget_isCocontinuous X.siteTopology K

/-- Continuity of the site functor of `φ : K ⟶ L` on packaged ringed sites. -/
instance overMap_isContinuous_site {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) :
    (overMap φ).IsContinuous (site K).siteTopology (site L).siteTopology :=
  SemiRepresentableFamily.overMap_isContinuous X.siteTopology φ

/-- Cocontinuity of the site functor of `φ : K ⟶ L` on packaged ringed sites. -/
instance overMap_isCocontinuous_site {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) :
    (overMap φ).IsCocontinuous (site K).siteTopology (site L).siteTopology :=
  SemiRepresentableFamily.overMap_isCocontinuous X.siteTopology φ

/-- Restricting `forget L` along `overMap φ` recovers `forget K`. -/
def forget_comp_overMap {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    overMap φ ⋙ SemiRepresentableFamily.forget L ≅ SemiRepresentableFamily.forget K :=
  CategoryTheory.Sigma.natIso fun i ↦
    (Functor.associator (overIncl K i) (overMap φ) (SemiRepresentableFamily.forget L)).symm ≪≫
    Functor.isoWhiskerRight (overMap_comp_incl φ i) (SemiRepresentableFamily.forget L) ≪≫
    Functor.associator (Over.map (φ.φ i)) (overIncl L (φ.f i))
      (SemiRepresentableFamily.forget L) ≪≫
    Functor.isoWhiskerLeft (Over.map (φ.φ i)) (forget_comp_incl L (φ.f i)) ≪≫
    Over.mapForget (φ.φ i) ≪≫
    (forget_comp_incl K i).symm

/-- The identification `O_K ≅ f⁻¹ O_L` for an SR-morphism `φ : K ⟶ L`. -/
def mapRingSheafIso {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    ringSheaf K ≅
      Cocontinuous.inverseImageRingSheaf
        (J := overTopology X.siteTopology K) (K := overTopology X.siteTopology L)
        (overMap φ) (ringSheaf L) :=
  (Functor.sheafPushforwardContinuousComp' (forget_comp_overMap φ) RingCat.{w}
    (overTopology X.siteTopology K) (overTopology X.siteTopology L)
    X.siteTopology).symm.app X.structureSheaf

/-- The localization morphism of ringed topoi
`j : (Sh(C / K), O_K) ⟶ (Sh(C), O_C)`. -/
def toAmbient (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology K) (Type w)]
    [∀ P : (OverSite K)ᵒᵖ ⥤ Type w,
      (SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [h_forget : (SemiRepresentableFamily.forget K).IsCocontinuous
      (site K).siteTopology X.siteTopology] :
    ToposHom (site K) X :=
  @Cocontinuous.toRingedTopos (site K) X
    (SemiRepresentableFamily.forget K) h_forget inferInstance
    inferInstance inferInstance inferInstance
    (𝟙 ((SemiRepresentableFamily.forget K).op ⋙ X.structureSheaf.obj))

/-- The structure-presheaf map of an SR-morphism, the underlying map of
`O_K ≅ f⁻¹ O_L`. -/
def mapStructurePresheafHom {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    (overMap φ).op ⋙ (site L).structureSheaf.obj ⟶ (site K).structureSheaf.obj :=
  (mapRingSheafIso φ).inv.hom

/-- The morphism of ringed topoi
`f : (Sh(C / K), O_K) ⟶ (Sh(C / L), O_L)` induced by `φ : K ⟶ L` in `SR(C)`. -/
def map {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology K) (Type w)]
    [∀ P : (OverSite K)ᵒᵖ ⥤ Type w,
      (overMap φ).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology L).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [h_map : (overMap φ).IsCocontinuous (site K).siteTopology (site L).siteTopology] :
    ToposHom (site K) (site L) :=
  @Cocontinuous.toRingedTopos (site K) (site L)
    (overMap φ) h_map inferInstance
    inferInstance inferInstance inferInstance
    (mapStructurePresheafHom φ)

/-- The inverse-image structure map of `toAmbient` is an isomorphism, encoding
`O_K = j⁻¹ O_C`. -/
@[instance]
theorem toAmbient_structureMap_isIso (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology K) (Type w)]
    [∀ P : (OverSite K)ᵒᵖ ⥤ Type w,
      (SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    IsIso (toAmbient K).structureMap := sorry

/-- The inverse-image structure map of `map φ` is an isomorphism, encoding
`O_K = f⁻¹ O_L`. -/
@[instance]
theorem map_structureMap_isIso {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology K) (Type w)]
    [∀ P : (OverSite K)ᵒᵖ ⥤ Type w,
      (overMap φ).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology L).HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    IsIso (map φ).structureMap := sorry

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The ambient extension presheaf has sections given by sums over pairs
consisting of a family component and an arrow into that component. -/
def moduleLowerShriekPresheaf (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] :
    SheafOfModules.{z} (ringSheaf K) ⥤ PresheafOfModules.{z} X.structureSheaf.obj where
  obj G :=
    { obj V := ∐ fun lift : Σ i : K.I, V.unop ⟶ K.obj i ↦
        G.val.obj (op ⟨lift.1, Over.mk lift.2⟩)
      map {V W} restriction := Limits.Sigma.desc
        (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj V))
        (f := fun lift : Σ i : K.I, V.unop ⟶ K.obj i ↦
          G.val.obj (op ⟨lift.1, Over.mk lift.2⟩)) fun lift ↦
        let source := G.val.obj (op ⟨lift.1, Over.mk lift.2⟩)
        let destination :=
          (_root_.ModuleCat.restrictScalars (X.structureSheaf.obj.map restriction).hom).obj
            (∐ fun target : Σ i : K.I, W.unop ⟶ K.obj i ↦
              (G.val.obj (op ⟨target.1, Over.mk target.2⟩) :
                _root_.ModuleCat.{z} (X.structureSheaf.obj.obj W)))
        @_root_.ModuleCat.ofHom _ _ source destination
          source.isAddCommGroup source.isModule
          destination.isAddCommGroup destination.isModule
          { toFun := fun element ↦
              Limits.Sigma.ι (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj W))
                (fun target : Σ i : K.I, W.unop ⟶ K.obj i ↦
                  G.val.obj (op ⟨target.1, Over.mk target.2⟩))
                ⟨lift.1, restriction.unop ≫ lift.2⟩
                (G.val.map (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
                  (Over.homMk (U := Over.mk (restriction.unop ≫ lift.2))
                    (V := Over.mk lift.2) restriction.unop (by rfl)) :
                    (⟨lift.1, Over.mk (restriction.unop ≫ lift.2)⟩ : OverSite K) ⟶
                      ⟨lift.1, Over.mk lift.2⟩)) element)
            map_add' := sorry
            map_smul' := sorry }
      map_id := sorry
      map_comp := sorry }
  map {G H} morphism :=
    { app V := Limits.Sigma.desc
        (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj V))
        (f := fun lift : Σ i : K.I, V.unop ⟶ K.obj i ↦
          G.val.obj (op ⟨lift.1, Over.mk lift.2⟩)) fun lift ↦
        morphism.val.app (op ⟨lift.1, Over.mk lift.2⟩) ≫
          Limits.Sigma.ι (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj V))
            (fun target : Σ i : K.I, V.unop ⟶ K.obj i ↦
              H.val.obj (op ⟨target.1, Over.mk target.2⟩)) lift
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Ambient extension of module sheaves is the sheafification of the
component-and-arrow-indexed direct-sum presheaf. -/
def moduleLowerShriek (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} X.structureSheaf :=
  moduleLowerShriekPresheaf K ⋙
    PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- Ambient extension is left adjoint to restriction to the family site,
with the Hom correspondence determined by the direct-sum inclusions. -/
def moduleLowerShriekAdjunction (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    moduleLowerShriek K ⊣
      Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K)
        X.structureSheaf :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F ↦
        { toFun := fun morphism ↦
            { val :=
                { app V := _root_.ModuleCat.ofHom
                    { toFun := fun element ↦
                        (PresheafOfModules.sheafificationHomEquiv
                          (𝟙 X.structureSheaf.obj) morphism).app (op V.unop.2.left)
                          (Limits.Sigma.ι
                            (C := _root_.ModuleCat.{z}
                              (X.structureSheaf.obj.obj (op V.unop.2.left)))
                            (fun lift : Σ i : K.I, V.unop.2.left ⟶ K.obj i ↦
                              G.val.obj (op ⟨lift.1, Over.mk lift.2⟩))
                            ⟨V.unop.1, V.unop.2.hom⟩ element)
                      map_add' := sorry
                      map_smul' := sorry }
                  naturality := sorry } }
          invFun := fun morphism ↦
            (PresheafOfModules.sheafificationHomEquiv
              (𝟙 X.structureSheaf.obj)).symm
              { app V := Limits.Sigma.desc
                  (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj V))
                  (f := fun lift : Σ i : K.I, V.unop ⟶ K.obj i ↦
                    G.val.obj (op ⟨lift.1, Over.mk lift.2⟩))
                  fun lift ↦ morphism.val.app (op ⟨lift.1, Over.mk lift.2⟩)
                naturality := sorry }
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The functor `j_! : Mod(O_K) ⥤ Mod(O_C)` is exact. -/
theorem moduleLowerShriek_exact (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    exactFunctor
      (SheafOfModules.{z} (ringSheaf K))
      (SheafOfModules.{z} X.structureSheaf)
      (moduleLowerShriek K) := sorry

/-- Change of coefficients along `O_K ≅ f⁻¹ O_L`, as modules on `C / K`. -/
def mapRingSheafModulesIso {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    SheafOfModules.{z} (ringSheaf K) ⥤
      SheafOfModules.{z}
        (Cocontinuous.inverseImageRingSheaf
          (J := overTopology X.siteTopology K) (K := overTopology X.siteTopology L)
          (overMap φ) (ringSheaf L)) :=
  SheafOfModules.pushforward (F := 𝟭 _)
    ((mapRingSheafIso φ).inv ≫
      (Functor.sheafPushforwardContinuousId RingCat.{w}
        (overTopology X.siteTopology K)).inv.app (ringSheaf K))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Relocalization extension before sheafification is the sum of sections
on source lifts of each target slice object. -/
def mapModuleLowerShriekPresheaf {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) [UnivLE.{max ι v, z}] :
    SheafOfModules.{z} (ringSheaf K) ⥤ PresheafOfModules.{z} (ringSheaf L).obj where
  obj G :=
    { obj V := ∐ fun lift : Σ i : K.I,
          {arrow : V.unop.2.left ⟶ K.obj i //
            (overMap φ).obj ⟨i, Over.mk arrow⟩ = V.unop} ↦
        G.val.obj (op ⟨lift.1, Over.mk lift.2.val⟩)
      map {V W} restriction := by
        rcases V with ⟨⟨index, targetSlice⟩⟩
        rcases W with ⟨⟨sourceIndex, sourceSlice⟩⟩
        cases Quiver.Hom.unop restriction with
        | mk arrow =>
          exact Limits.Sigma.desc
            (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op targetSlice.left)))
            (f := fun lift : Σ i : K.I,
                {liftArrow : targetSlice.left ⟶ K.obj i //
                  (overMap φ).obj ⟨i, Over.mk liftArrow⟩ = ⟨index, targetSlice⟩} ↦
              G.val.obj (op ⟨lift.1, Over.mk lift.2.val⟩)) fun lift ↦
            let source := G.val.obj (op ⟨lift.1, Over.mk lift.2.val⟩)
            let destination :=
              (_root_.ModuleCat.restrictScalars ((ringSheaf L).obj.map restriction).hom).obj
                (∐ fun target : Σ i : K.I,
                    {liftArrow : sourceSlice.left ⟶ K.obj i //
                      (overMap φ).obj ⟨i, Over.mk liftArrow⟩ = ⟨index, sourceSlice⟩} ↦
                  (G.val.obj (op ⟨target.1, Over.mk target.2.val⟩) :
                    _root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op sourceSlice.left))))
            @_root_.ModuleCat.ofHom _ _ source destination
              source.isAddCommGroup source.isModule
              destination.isAddCommGroup destination.isModule
              { toFun := fun element ↦
                  Limits.Sigma.ι
                    (C := _root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op sourceSlice.left)))
                    (fun target : Σ i : K.I,
                        {liftArrow : sourceSlice.left ⟶ K.obj i //
                          (overMap φ).obj ⟨i, Over.mk liftArrow⟩ = ⟨index, sourceSlice⟩} ↦
                      G.val.obj (op ⟨target.1, Over.mk target.2.val⟩))
                    ⟨lift.1, ⟨arrow.left ≫ lift.2.val, by sorry⟩⟩
                    (G.val.map (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
                      (Over.homMk (U := Over.mk (arrow.left ≫ lift.2.val))
                        (V := Over.mk lift.2.val) arrow.left (by rfl)) :
                        (⟨lift.1, Over.mk (arrow.left ≫ lift.2.val)⟩ : OverSite K) ⟶
                          ⟨lift.1, Over.mk lift.2.val⟩)) element)
                map_add' := sorry
                map_smul' := sorry }
      map_id := sorry
      map_comp := sorry }
  map {G H} morphism :=
    { app V := Limits.Sigma.desc (C := _root_.ModuleCat.{z} ((ringSheaf L).obj.obj V)) fun lift ↦
        morphism.val.app (op ⟨lift.1, Over.mk lift.2.val⟩) ≫
          Limits.Sigma.ι (C := _root_.ModuleCat.{z} ((ringSheaf L).obj.obj V))
            (fun target : Σ i : K.I,
                {arrow : V.unop.2.left ⟶ K.obj i //
                  (overMap φ).obj ⟨i, Over.mk arrow⟩ = V.unop} ↦
              H.val.obj (op ⟨target.1, Over.mk target.2.val⟩)) lift
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Extension along a morphism of families is the sheafification of the
presheaf of direct sums over its component lifts. -/
def mapModuleLowerShriek {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L)
    [UnivLE.{max ι v, z}]
    [HasWeakSheafify (overTopology X.siteTopology L) AddCommGrpCat.{z}]
    [(overTopology X.siteTopology L).WEqualsLocallyBijective AddCommGrpCat.{z}] :
    SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} (ringSheaf L) :=
  mapModuleLowerShriekPresheaf φ ⋙
    PresheafOfModules.sheafification (𝟙 (ringSheaf L).obj)

/-- Inverse image of modules along an SR-morphism, as a functor
`Mod(O_L) ⥤ Mod(O_K)`. -/
def mapModulePullback {K L : Limits.FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    SheafOfModules.{z} (ringSheaf L) ⥤ SheafOfModules.{z} (ringSheaf K) :=
  Cocontinuous.moduleInverseImage
      (J := overTopology X.siteTopology K) (K := overTopology X.siteTopology L)
      (overMap φ) (ringSheaf L) ⋙
    SheafOfModules.pushforward (F := 𝟭 _)
      ((mapRingSheafIso φ).hom ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology K)).inv.app
          (Cocontinuous.inverseImageRingSheaf
            (J := overTopology X.siteTopology K) (K := overTopology X.siteTopology L)
            (overMap φ) (ringSheaf L)))

/-- The functor `f_! : Mod(O_K) ⥤ Mod(O_L)` induced by `φ : K ⟶ L` is exact. -/
theorem map_moduleLowerShriek_exact {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) [UnivLE.{max ι v, z}]
    [HasWeakSheafify (overTopology X.siteTopology L) AddCommGrpCat.{z}]
    [(overTopology X.siteTopology L).WEqualsLocallyBijective AddCommGrpCat.{z}] :
    exactFunctor
      (SheafOfModules.{z} (ringSheaf K))
      (SheafOfModules.{z} (ringSheaf L))
      (mapModuleLowerShriek φ) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Extension along a family morphism is left adjoint to its module
restriction, by evaluation on lift summands and the sheafification adjunction. -/
def mapModuleLowerShriek_adjunction {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) [UnivLE.{max ι v, z}]
    [HasWeakSheafify (overTopology X.siteTopology L) AddCommGrpCat.{z}]
    [(overTopology X.siteTopology L).WEqualsLocallyBijective AddCommGrpCat.{z}] :
    mapModuleLowerShriek φ ⊣ mapModulePullback φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F ↦
        { toFun := fun morphism ↦
            { val :=
                { app V := @_root_.ModuleCat.ofHom _ _
                    (G.val.obj V) (((mapModulePullback φ).obj F).val.obj V)
                    (G.val.obj V).isAddCommGroup (G.val.obj V).isModule
                    (((mapModulePullback φ).obj F).val.obj V).isAddCommGroup
                    (((mapModulePullback φ).obj F).val.obj V).isModule
                    { toFun := fun element ↦
                        (PresheafOfModules.sheafificationHomEquiv
                          (𝟙 (ringSheaf L).obj) morphism).app
                          (op ((overMap φ).obj V.unop))
                          (Limits.Sigma.ι
                            (C := _root_.ModuleCat.{z} ((ringSheaf L).obj.obj
                              (op ((overMap φ).obj V.unop))))
                            (fun lift : Σ i : K.I,
                                {arrow : V.unop.2.left ⟶ K.obj i //
                                  (overMap φ).obj ⟨i, Over.mk arrow⟩ =
                                    (overMap φ).obj V.unop} ↦
                              G.val.obj (op ⟨lift.1, Over.mk lift.2.val⟩))
                            ⟨V.unop.1, ⟨V.unop.2.hom, rfl⟩⟩ element)
                      map_add' := sorry
                      map_smul' := sorry }
                  naturality := sorry } }
          invFun := fun morphism ↦
            (PresheafOfModules.sheafificationHomEquiv
              (𝟙 (ringSheaf L).obj)).symm
              { app V := Limits.Sigma.desc
                  (C := _root_.ModuleCat.{z} ((ringSheaf L).obj.obj V))
                  (f := fun lift : Σ i : K.I,
                      {arrow : V.unop.2.left ⟶ K.obj i //
                        (overMap φ).obj ⟨i, Over.mk arrow⟩ = V.unop} ↦
                    G.val.obj (op ⟨lift.1, Over.mk lift.2.val⟩))
                  fun lift ↦ _root_.ModuleCat.ofHom
                    { toFun := fun element ↦
                        cast (congrArg (fun target ↦ (F.val.obj (op target)).carrier)
                          lift.2.property)
                          (morphism.val.app (op ⟨lift.1, Over.mk lift.2.val⟩) element)
                      map_add' := sorry
                      map_smul' := sorry }
                naturality := sorry }
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The functor `j^* : Mod(O_C) ⥤ Mod(O_K)` is exact, so `j` is a flat morphism of
ringed topoi. -/
theorem toAmbient_modulePullback_exact (K : Limits.FormalCoproduct.{ι} X.carrier) :
    exactFunctor
      (SheafOfModules.{z} X.structureSheaf)
      (SheafOfModules.{z} (ringSheaf K))
      (Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K)
        X.structureSheaf) := sorry

/-- The functor `f^* : Mod(O_L) ⥤ Mod(O_K)` is exact, so `f` is a flat morphism of
ringed topoi. -/
theorem map_modulePullback_exact {K L : Limits.FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) :
    exactFunctor
      (SheafOfModules.{z} (ringSheaf L))
      (SheafOfModules.{z} (ringSheaf K))
      (mapModulePullback φ) := sorry

/-- Continuity of the composite `overIncl i ⋙ forget K`. -/
instance overIncl_comp_forget_isContinuous
    (K : Limits.FormalCoproduct.{ι} X.carrier) (i : K.I) :
    (overIncl K i ⋙ SemiRepresentableFamily.forget K).IsContinuous
      (X.siteTopology.over (K.obj i)) X.siteTopology :=
  @Functor.isContinuous_comp _ _ _ _ _ _
    (overIncl K i) (SemiRepresentableFamily.forget K)
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K) X.siteTopology
    (CategoryTheory.Sigma.incl_isContinuous
      (fun index : K.I ↦ X.siteTopology.over (K.obj index)) i)
    (SemiRepresentableFamily.forget_isContinuous X.siteTopology K)

/-- Comparison identifying restriction of `j^*` to a slice with `j_i^*`. -/
def sliceInverseImageComparison (K : Limits.FormalCoproduct.{ι} X.carrier) (i : K.I)
    (G : SheafOfModules.{z} X.structureSheaf) :
    (component K i).obj
      ((Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K)
        X.structureSheaf).obj G) ≅
      (Cocontinuous.moduleInverseImage (Over.forget (K.obj i)) X.structureSheaf).obj G :=
  (@SheafOfModules.pushforwardComp _ _ _ _ _ _
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K) (overIncl K i) _ _
    (CategoryTheory.Sigma.incl_isContinuous
      (fun index : K.I ↦ X.siteTopology.over (K.obj index)) i)
    (componentRingIso K i).hom X.siteTopology (SemiRepresentableFamily.forget K) _
    inferInstance (𝟙 (ringSheaf K))).app G ≪≫
  (SheafOfModules.pushforwardCongr₂
    (𝟙 (X.structureSheaf.over (K.obj i))) (forget_comp_incl K i) sorry).symm.app G

/-- Component of the coproduct comparison for `j_!`, adjunct to restriction of the
unit of `j_! ⊣ j^*`. -/
def moduleLowerShriekCoprodComponent (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [UnivLE.{v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))
    (i : K.I) :
    (SheafOfModules.Localization.lowerShriekDirectSum X.structureSheaf (K.obj i)).obj (F i) ⟶
      (moduleLowerShriek K).obj ((modulesEquiv K).inverse.obj F) :=
  ((SheafOfModules.Localization.lowerShriekDirectSumAdjunction
      X.structureSheaf (K.obj i)).homEquiv (F i) _).symm
    ((modulesCounitInvApp K F i) ≫
      (component K i).map
        ((moduleLowerShriekAdjunction K).unit.app
          ((modulesEquiv K).inverse.obj F)) ≫
      (sliceInverseImageComparison K i
        ((moduleLowerShriek K).obj ((modulesEquiv K).inverse.obj F))).hom)

/-- The comparison morphism `⊕ᵢ j_{i,!} F_i ⟶ j_! (F_i)_i` of the coproduct formula
for `j_!`. -/
def moduleLowerShriekCoprod (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [UnivLE.{v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))
    [HasCoproduct
      fun i : K.I ↦
        (SheafOfModules.Localization.lowerShriekDirectSum X.structureSheaf (K.obj i)).obj (F i)] :
    (∐ fun i : K.I ↦
        (SheafOfModules.Localization.lowerShriekDirectSum X.structureSheaf (K.obj i)).obj (F i)) ⟶
      (moduleLowerShriek K).obj ((modulesEquiv K).inverse.obj F) :=
  Limits.Sigma.desc fun i ↦ moduleLowerShriekCoprodComponent K F i

/-- The coproduct comparison for `j_!` is an isomorphism:
`j_! (F_i)_i ≅ ⊕ᵢ j_{i,!} F_i`. -/
@[instance]
theorem moduleLowerShriekCoprod_isIso (K : Limits.FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι v, z}] [UnivLE.{v, z}] [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))
    [HasCoproduct
      fun i : K.I ↦
        (SheafOfModules.Localization.lowerShriekDirectSum X.structureSheaf (K.obj i)).obj (F i)] :
    IsIso (moduleLowerShriekCoprod K F) := sorry

/-- The localization of a ringed site at a singleton family `{U}` compares to the
ordinary slice localization at `U`. -/
def singletonFunctor {U : X} :
    OverSite ((Limits.FormalCoproduct.incl.{ι} X.carrier).obj U) ⥤ Over U :=
  CategoryTheory.Sigma.desc fun _ ↦ 𝟭 _

/-- Slice inclusion of `C / U` into the localization category at the singleton `{U}`. -/
def singletonInverse {U : X} :
    Over U ⥤ OverSite ((Limits.FormalCoproduct.incl.{ι} X.carrier).obj U) :=
  @CategoryTheory.Sigma.incl PUnit.{ι + 1} (fun _ ↦ Over U) _ PUnit.unit

end RingedSite.Localization.AtSR
