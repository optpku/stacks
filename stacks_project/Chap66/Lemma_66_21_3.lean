/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SchemeComparison
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
  (AlgebraicGeometry.AlgebraicSpace.structureFMap_app :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f),
      (structureSheaf Y).obj.obj (op sq.right) ⟶
        (structureSheaf X).obj.obj (op sq.left))

#check
  (AlgebraicGeometry.AlgebraicSpace.structureSheafMap_app :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (V : (smallEtaleSite Y)ᵒᵖ),
      (structureSheaf Y).obj.obj V ⟶
        ((ringPushforward f).obj (structureSheaf X)).obj.obj V)

/- Lemma 66.21.3 (2): the canonical morphism of small étale ringed topoi is compatible
with composition. -/
@[stacks 03G8] #check
  (AlgebraicGeometry.AlgebraicSpace.ringedToposHomCompIso :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z),
    RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (ringedToposHom f) (ringedToposHom g))
      (ringedToposHom (f ≫ g)))

#check
  (AlgebraicGeometry.AlgebraicSpace.ringedToposHomIdIso :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u} (ringedToposHom (𝟙 X))
      (RingedSite.ToposHom.id (ringedSite X)))

#check
  (AlgebraicGeometry.AlgebraicSpace.ringPushforwardObjOfSchemeEtaleIso :
    ∀ {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale),
    ((ringPushforward (ofOverHomMk f hf)).obj
        (structureSheaf (ofOver (Over.mk σX)))).obj.obj
      (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≅
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (Small.structureSheaf X)).obj.obj (op V))

/- Lemma 66.21.3 (3): for a scheme morphism over the base, the transported direct-image
structure map agrees with the scheme small étale structure map of Descent, Remark 35.8.4.
This direct-image map is the mate of the inverse-image structure map `f^♯`. -/
@[stacks 03G8] #check
  (AlgebraicGeometry.AlgebraicSpace.structureSheafMap_app_ofOverHomMk :
    ∀ {S : Scheme.{u}} {X Y : Scheme.{u}}
    {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX) (V : Y.Etale),
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          ((schemeEtaleToSmallEtale_schemeProjection (Over.mk σY)).app V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≫
        (ringPushforwardObjOfSchemeEtaleIso f hf V).hom =
      (Small.ringedHom f).structureSheafMap.hom.app (op V))

/- Lemma 66.21.3 (3): the scheme comparison identifies the transported structure map
with pullback of global sections along the fibre-product projection. -/
@[stacks 03G8] #check
  (AlgebraicGeometry.AlgebraicSpace.structureSheafMap_app_ofOverHomMk_eq_appTop :
    ∀ {S : Scheme.{u}}
    {X Y : Scheme.{u}} {σX : X ⟶ S} {σY : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ σY = σX)
    (V : Y.Etale),
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          ((schemeEtaleToSmallEtale_schemeProjection (Over.mk σY)).app V).op ≫
        structureSheafMap_app (ofOverHomMk f hf)
          (op (schemeEtaleToSmallEtaleObj (Over.mk σY) V)) ≫
        (ringPushforwardObjOfSchemeEtaleIso f hf V).hom =
      RingCat.ofHom (pullback.fst V.hom f).appTop.hom)
