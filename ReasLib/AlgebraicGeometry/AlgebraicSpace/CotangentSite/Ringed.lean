/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Cotangent
variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The map of presheaves induced by pulling affine-target functions back to étale charts. -/
def structurePresheafMap : structurePresheaf Λ X ⟶ underlinePresheaf Λ X where
  app P := (CommRingCat.universeLift.{u, u + 1}).map
    (Scheme.Γ.map (op (unop P).hom.left))
  naturality := by sorry

/-- The morphism between the sheafifications induced by the chart-to-affine morphisms.
Its comparison with raw global sections is mediated by the sheafification units. -/
noncomputable def structureSheafMap : structureSheaf Λ X ⟶ underlineSheaf Λ X :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).map (structurePresheafMap Λ X)

/-- The structure-sheaf morphism with successor-universe coefficients. -/
abbrev structureSheafMapLift := structureSheafMap Λ X
/-- The raw structure-presheaf morphism with successor-universe coefficients. -/
abbrev structurePresheafMapLift := structurePresheafMap Λ X

/-- Forgetting commutativity preserves sheaves on the cotangent site. -/
instance topology_hasSheafCompose_comm :
    (topology Λ X).HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  infer_instance

/-- Forgetting ring structure preserves sheaves on the cotangent site. -/
instance topology_hasSheafCompose_forget :
    (topology Λ X).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) := by
  infer_instance

/-- Forgetting ring structure preserves sheaves on the small étale site. -/
instance smallEtaleTopology_hasSheafCompose_forget :
    (smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) := by
  infer_instance

/-- Type-valued presheaves admit pointwise right Kan extension along the étale projection. -/
instance forget_op_hasPointwiseRightKanExtension
    (P : (category Λ X)ᵒᵖ ⥤ Type (u + 1)) :
    (forget Λ X).op.HasPointwiseRightKanExtension P := by
  sorry

/-- The underlying ring-valued presheaf of affine-target functions. -/
def structurePresheafRing : (category Λ X)ᵒᵖ ⥤ RingCat.{u + 1} :=
  structurePresheaf Λ X ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The underlying ring-valued structure presheaf pulled back from étale charts. -/
def underlinePresheafRing : (category Λ X)ᵒᵖ ⥤ RingCat.{u + 1} :=
  underlinePresheaf Λ X ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The ring-valued sheaf underlying the sheafified affine-target structure sheaf. -/
def structureSheafRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (structureSheaf Λ X)

/-- The ring-valued sheaf underlying the sheafified pulled-back structure sheaf. -/
def underlineSheafRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (underlineSheaf Λ X)

/-- The continuous pullback of the underlying ring sheaf of the lifted étale structure sheaf. -/
abbrev underlineInverseImageRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  ((forget Λ X).sheafPushforwardContinuous RingCat.{u + 1}
    (topology Λ X) (smallEtaleTopology X)).obj
      (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (commStructureSheafLift X))

/-- The underlying ring isomorphism between the sheafified pulled-back structure sheaf
and the continuous pullback of the lifted étale structure sheaf. -/
noncomputable def underlineRingIso :
    underlineSheafRing Λ X ≅ underlineInverseImageRing Λ X :=
  (sheafCompose (topology Λ X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (underlineSheafIso Λ X)

/-- The canonical comparison from the sheafified pulled-back ring sheaf to the continuous
pullback of the lifted étale ring sheaf. -/
noncomputable def underlineRingComparison :
    underlineSheafRing Λ X ⟶ underlineInverseImageRing Λ X :=
  (underlineRingIso Λ X).hom

/-- The inverse canonical comparison from the continuous pullback of the lifted étale ring
sheaf to the sheafified pulled-back ring sheaf. -/
noncomputable def underlineRingComparisonInv :
    underlineInverseImageRing Λ X ⟶ underlineSheafRing Λ X :=
  (underlineRingIso Λ X).inv

/-- The morphism of ring sheaves induced by pulling affine-target functions back to charts. -/
def structureSheafMapRing : structureSheafRing Λ X ⟶ underlineSheafRing Λ X :=
  CategoryTheory.Sheaf.ringSheafOfCommMap.{u + 1, u + 1, u} (structureSheafMap Λ X)

/-- The cotangent site equipped with the sheafification of affine-target global functions. -/
abbrev ringedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (topology Λ X) (structureSheafRing Λ X)

/-- The cotangent site equipped with the sheafified pulled-back structure sheaf. -/
abbrev underlineRingedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (topology Λ X) (underlineSheafRing Λ X)

/-- The morphism of ringed sites induced by the chart-to-affine structure map on one site. -/
def sameSite : underlineRingedSite Λ X ⟶ ringedSite Λ X :=
  RingedSite.SameSite.hom (structureSheafMapRing Λ X)

/-- The morphism of ringed topoi induced by the structure-sheaf map on the cotangent site. -/
def i : ToposHom (underlineRingedSite Λ X) (ringedSite Λ X) :=
  Hom.toToposHom (sameSite Λ X)

/-- The projection from the cotangent site to the small étale site of the algebraic space. -/
def forgetOnSites : underlineRingedSite Λ X ⥤ commRingedSiteLift X := forget Λ X

/-- The comparison from the pulled-back étale structure presheaf to its sheafification,
obtained from the canonical sheafification unit. -/
def underlineComparison :
    (forgetOnSites Λ X).op ⋙ (commRingedSiteLift X).structureSheaf.obj ⟶
      (underlineRingedSite Λ X).structureSheaf.obj :=
  Functor.whiskerRight (underlineSheafUnit Λ X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The projection from polynomial affine presentations to étale charts is cocontinuous. -/
instance forgetOnSites_isCocontinuous :
    (forgetOnSites Λ X).IsCocontinuous
      (underlineRingedSite Λ X).siteTopology (commRingedSiteLift X).siteTopology := by
  sorry

/-- Type-valued presheaves admit pointwise right Kan extension along the site projection. -/
instance forgetOnSites_op_hasPointwiseRightKanExtension
    (P : (underlineRingedSite Λ X)ᵒᵖ ⥤ Type (u + 1)) :
    (forgetOnSites Λ X).op.HasPointwiseRightKanExtension P := by
  sorry

/-- Type-valued presheaves on the cotangent ringed site admit sheafification. -/
instance underlineRingedSite_hasSheafify :
    HasSheafify (underlineRingedSite Λ X).siteTopology (Type (u + 1)) := by
  infer_instance

/-- The forgetful functor from rings to types preserves sheaves on the cotangent ringed site. -/
instance underlineRingedSite_hasSheafCompose :
    (underlineRingedSite Λ X).siteTopology.HasSheafCompose
      (CategoryTheory.forget RingCat.{u + 1}) := by
  infer_instance

/-- The forgetful functor from rings to types preserves sheaves on the lifted étale ringed site. -/
instance commRingedSiteLift_hasSheafCompose :
    (commRingedSiteLift X).siteTopology.HasSheafCompose
      (CategoryTheory.forget RingCat.{u + 1}) := by
  infer_instance

/-- The morphism of ringed topoi from the cotangent site to the small étale site,
whose structure map is induced by the canonical sheafification unit. -/
def π : ToposHom (underlineRingedSite Λ X) (commRingedSiteLift X) :=
  Cocontinuous.toRingedTopos (forgetOnSites Λ X) (underlineComparison Λ X)

/-- The site morphism inducing the same-site ringed-topos morphism is the identity functor. -/
theorem i_base : (sameSite Λ X).base = 𝟭 (category Λ X) := sorry

/-- The site functor inducing the ringed-topos projection is the étale-chart projection. -/
theorem π_base : forgetOnSites Λ X = forget Λ X := rfl

/-- The structure comparison for the ringed-topos projection is the underlying ring map
of the canonical sheafification unit. -/
theorem π_structureMap :
    underlineComparison Λ X =
      Functor.whiskerRight (underlineSheafUnit Λ X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := rfl

end AlgebraicGeometry.AlgebraicSpace.Cotangent
