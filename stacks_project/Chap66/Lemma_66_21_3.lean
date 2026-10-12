/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open Scheme.Etale

noncomputable section

/- Lemma 66.21.3 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Then there is a canonical map `f^♯ : f_small⁻¹ 𝒪_Y ⟶ 𝒪_X` such that
`(f_small, f^♯)` is a morphism of small étale ringed topoi. This is
`ringedToposHom f : RingedSite.ToposHom (ringedSite X) (ringedSite Y)`, with
`f_small = (ringedToposHom f).toTopos` and `f^♯ = (ringedToposHom f).structureMap`.
The inverse-image map `f^♯` is the mate of the direct-image map `structureSheafMap f`,
whose component at `V` is `structureSheafMap_app f`. -/
@[stacks 03G8] #check
  (AlgebraicGeometry.AlgebraicSpace.ringedToposHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → RingedSite.ToposHom (ringedSite X) (ringedSite Y))

#check
  (fun {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) ↦
    (ringedToposHom f).toTopos)

#check
  (fun {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) ↦
    (ringedToposHom f).structureMap)

#check AlgebraicGeometry.AlgebraicSpace.structureFMap_app

#check AlgebraicGeometry.AlgebraicSpace.structureSheafMap_app

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.21.3 (2): the construction `f ↦ (f_small, f^♯)` is compatible with
compositions of morphisms of algebraic spaces over `S`. -/
@[stacks 03G8]
theorem ringedToposHom_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    RingedSite.ToposHom.comp (ringedToposHom f) (ringedToposHom g) =
      ringedToposHom (f ≫ g) :=
  sorry

/-- The morphism of small étale ringed topoi associated to the identity of an algebraic
space is the identity morphism of ringed topoi. -/
theorem ringedToposHom_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ringedToposHom (𝟙 X) = RingedSite.ToposHom.id (ringedSite X) :=
  sorry

/-- `ofOverMap` of an étale morphism of schemes over `S` is étale as a morphism of
algebraic spaces. -/
theorem etale_ofOverMap_overHomMk {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    Etale (ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U)) :=
  sorry

/-- The object of the small étale site of `ofOver U` associated to a scheme étale over
`U.left`. -/
def smallEtaleSite.ofSchemeEtale {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    smallEtaleSite (ofOver U) :=
  MorphismProperty.CostructuredArrow.mk ⊤
    (ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U))
    (etale_ofOverMap_overHomMk U W)

/-- The structural morphism of `smallEtaleSite.ofSchemeEtale U W` is `ofOverMap` of the
over-morphism induced by `W.hom`. -/
theorem smallEtaleSite.ofSchemeEtale_hom {S : Scheme.{u}} (U : Over S)
    (W : U.left.Etale) :
    (smallEtaleSite.ofSchemeEtale U W).hom =
      ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U) :=
  sorry

/-- Identity comparison of the underlying scheme of `W` with its algebraic-space
realization. -/
def smallEtaleSite.ofSchemeEtale_schemeHom {S : Scheme.{u}} (U : Over S)
    (W : U.left.Etale) :
    (smallEtaleToScheme (ofOver U)).obj (smallEtaleSite.ofSchemeEtale U W) ⟶
      (Scheme.smallEtaleToScheme U.left).obj W :=
  (𝟙 W.left :
    (smallEtaleToScheme (ofOver U)).obj (smallEtaleSite.ofSchemeEtale U W) ⟶
      (Scheme.smallEtaleToScheme U.left).obj W)

/-- `smallEtaleSite.ofSchemeEtale_schemeHom` is the identity of the underlying scheme of
`W`. -/
theorem smallEtaleSite.ofSchemeEtale_schemeHom_apply {S : Scheme.{u}} (U : Over S)
    (W : U.left.Etale) :
    smallEtaleSite.ofSchemeEtale_schemeHom U W =
      (𝟙 W.left :
        (smallEtaleToScheme (ofOver U)).obj (smallEtaleSite.ofSchemeEtale U W) ⟶
          (Scheme.smallEtaleToScheme U.left).obj W) :=
  sorry

/-- Direct-image structure-sheaf values of `ofOverHomMk f hf` at the algebraic-space
object associated to `V` agree with the small étale direct image of
`Small.ringedHom f` at `V`. -/
theorem ringPushforward_obj_ofSchemeEtale {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale) :
    ((ringPushforward (ofOverHomMk f hf)).obj
        (structureSheaf (ofOver (Over.mk σX)))).obj.obj
      (op (smallEtaleSite.ofSchemeEtale (Over.mk σY) V)) =
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (Small.structureSheaf X)).obj.obj (op V) :=
  sorry

/-- Lemma 66.21.3 (3): if `f` is a morphism of schemes over `S`, then `f^♯` is the map of
Descent, Remark 35.8.4. On `V : Y.Etale`, the direct-image component
`structureSheafMap_app (ofOverHomMk f hf)` at the algebraic-space object associated to
`V`, transported along the identity-on-underlying-schemes comparison, equals
`(Small.ringedHom f).structureSheafMap.hom.app (op V)`, hence equals
`RingCat.ofHom (pullback.fst V.hom f).appTop.hom`. This direct-image map is the mate of
`(ringedToposHom (ofOverHomMk f hf)).structureMap`. -/
@[stacks 03G8]
theorem structureSheafMap_app_ofOverHomMk {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale) :
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          (smallEtaleSite.ofSchemeEtale_schemeHom (Over.mk σY) V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (smallEtaleSite.ofSchemeEtale (Over.mk σY) V)) ≫
        eqToHom (ringPushforward_obj_ofSchemeEtale f hf V) =
      (Small.ringedHom f).structureSheafMap.hom.app (op V) :=
  sorry

/-- On a scheme morphism, the transported algebraic-space direct-image component is the
fibre-product projection on global sections from Descent, Remark 35.8.4. -/
theorem structureSheafMap_app_ofOverHomMk_eq_appTop {S : Scheme.{u}}
    {X Y : Scheme.{u}} {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX)
    (V : Y.Etale) :
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          (smallEtaleSite.ofSchemeEtale_schemeHom (Over.mk σY) V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (smallEtaleSite.ofSchemeEtale (Over.mk σY) V)) ≫
        eqToHom (ringPushforward_obj_ofSchemeEtale f hf V) =
      RingCat.ofHom (pullback.fst V.hom f).appTop.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
