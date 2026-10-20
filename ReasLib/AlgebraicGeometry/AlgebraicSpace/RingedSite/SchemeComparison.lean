module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Comparison of algebraic-space and scheme small étale structure maps

For a morphism of schemes over a fixed base, the algebraic-space structure-sheaf map
agrees with the scheme small étale structure-sheaf map on the canonical scheme charts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme.Etale

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Direct-image structure-sheaf values on a scheme chart of an algebraic space are
canonically isomorphic to the corresponding scheme small étale direct-image values. -/
def ringPushforwardObjOfSchemeEtaleIso {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale) :
    ((ringPushforward (ofOverHomMk f hf)).obj
        (structureSheaf (ofOver (Over.mk σX)))).obj.obj
      (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≅
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (Small.structureSheaf X)).obj.obj (op V) := by
  let X' := ofOver (Over.mk σX)
  let f' := ofOverHomMk f hf
  let V' := schemeEtaleToSmallEtaleObj (Over.mk σY) V
  let W := (etaleBaseChange f').obj V'
  let Q := EtaleRingedTopos.structureTypes X'
  let U := schemeEtaleToSmallEtaleObj (Over.mk σX) ((Scheme.smallEtalePullback f).obj V)
  let a : (smallEtaleToSpaces X').obj U ⟶ W :=
    MorphismProperty.Over.homMk
      (pullback.lift (f := homFunctor f') (g := homFunctor V'.hom)
        U.hom (ofOverMap (Over.homMk (pullback.fst V.hom f) (by sorry)))
        (by sorry)) (by sorry)
  let e := ((ringPushforwardForgetIso f').app (structureSheaf X'))
  let forward := e.hom.hom.app (op V') ≫ EtaleTopos.extensionEvaluation X' Q a
  let c : Cone (StructuredArrow.proj (op W) (smallEtaleToSpaces X').op ⋙ Q.obj) :=
    { pt := (Q.obj.obj (op U))
      π :=
        { app := fun b ↦
            let toX : b.right.unop.left ⟶ Over.mk σX :=
              yoneda.preimage (b.hom.unop.left ≫ etaleBaseChangeFst f' V')
            let toV : b.right.unop.left ⟶ V'.left :=
              yoneda.preimage (b.hom.unop.left ≫ etaleBaseChangeSnd f' V')
            let toPullback : b.right.unop.left.left ⟶ pullback V.hom f :=
              pullback.lift toV.left toX.left (by sorry)
            TypeCat.ofHom toPullback.appTop.hom
          naturality := by sorry } }
  let backward := EtaleTopos.allChartLift X' Q W c ≫ e.inv.hom.app (op V')
  let A := ((ringPushforward f').obj (structureSheaf X')).obj.obj (op V')
  let B := (((Scheme.smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj (Small.structureSheaf X)).obj.obj (op V)
  exact
    { hom := @RingCat.ofHom A B _ _
        { toFun := forward
          map_one' := by sorry
          map_mul' := by sorry
          map_zero' := by sorry
          map_add' := by sorry }
      inv := @RingCat.ofHom B A _ _
        { toFun := backward
          map_one' := by sorry
          map_mul' := by sorry
          map_zero' := by sorry
          map_add' := by sorry }
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

/-- On a scheme morphism over a fixed base, the algebraic-space direct-image structure
map, transported along the canonical scheme-chart comparisons, equals the scheme
small étale structure map. -/
theorem structureSheafMap_app_ofOverHomMk {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale) :
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          ((schemeEtaleToSmallEtale_schemeProjection (Over.mk σY)).app V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≫
        (ringPushforwardObjOfSchemeEtaleIso f hf V).hom =
      (Small.ringedHom f).structureSheafMap.hom.app (op V) :=
  sorry

/-- On a scheme morphism over a fixed base, the transported algebraic-space direct-image
structure map is pullback of global sections along the fibre-product projection. -/
theorem structureSheafMap_app_ofOverHomMk_eq_appTop {S : Scheme.{u}}
    {X Y : Scheme.{u}} {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX)
    (V : Y.Etale) :
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          ((schemeEtaleToSmallEtale_schemeProjection (Over.mk σY)).app V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≫
        (ringPushforwardObjOfSchemeEtaleIso f hf V).hom =
      RingCat.ofHom (pullback.fst V.hom f).appTop.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
