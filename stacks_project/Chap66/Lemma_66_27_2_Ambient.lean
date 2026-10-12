/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap66.Lemma_66_27_2_SchemeBridge
public import stacks_project.Chap66.Lemma_66_27_2_Slice

/-! # The ambient inverse-image comparison at the actual small-site parameter -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}}

/-- Extension to spaces commutes with restriction to a representable slice.
This is the mate of the literal `Over.post`/forget square. -/
def extensionOverIso (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    (smallEtaleTopology X).overPullback (Type u) U ⋙
        (smallEtaleLocalizationSheafEquivalence X U).inverse ≅
      (inclusionEquivalence X).inverse ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((smallEtaleInclusion X).obj U) :=
  (inclusionEquivalence X).transferSquare (smallEtaleLocalizationSheafEquivalence X U) _ _
    ((smallEtaleInclusion X).sheafPushforwardOverPostComp U (Type u))

/-- The transported spaces inverse image is compared with the specified small inverse image
by uniqueness of the left adjoint to the existing direct-image comparison. -/
def morphismInverseImageIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (inclusionEquivalence Y).inverse ⋙ (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (inclusionEquivalence X).functor ≅ (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    ((((inclusionEquivalence Y).symm.toAdjunction.comp
      (spacesRingedToposHom f).toTopos.adjunction).comp
        (inclusionEquivalence X).toAdjunction).ofNatIsoRight (morphismPushforwardIso f).symm)
    (morphismOfTopoi f).adjunction

/-- Relocalization has restriction as its inverse image, with its specified right adjoint. -/
def relocalizationInverseImageIso {X : AlgebraicSpace S} {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (spacesRingedHom.relocalization c).toTopos.inverseImage ≅
      (Over.map c).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) :=
  Adjunction.leftAdjointUniq (spacesRingedHom.relocalization c).toTopos.adjunction
    ((Over.map c).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V))

/-- The actual mate for the ambient square of spaces-site localization; no inverse is chosen. -/
def spacesLocalizationComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : spacesEtaleSite Y) :
    (spacesEtaleTopology Y).overPullback (Type u) V ⋙
        (spacesRingedHom.localizationToposHom f V).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((spacesEtalePullback f).obj V) :=
  ((mateEquiv (spacesRingedToposHom f).toTopos.adjunction
    (spacesRingedHom.localizationToposHom f V).toTopos.adjunction).symm
      ((spacesEtalePullback f).sheafPushforwardOverPostComp V (Type u)).inv).natTrans

/-- The ambient square for spaces localization at an actual site arrow.
It is formed from the previous mate and strict restriction along `Over.map c`. -/
def spacesAtComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : spacesEtaleSite Y)
    {U : spacesEtaleSite X} (c : U ⟶ (spacesEtalePullback f).obj V) :
    (spacesEtaleTopology Y).overPullback (Type u) V ⋙
        (spacesRingedHom.localizationAt f V c).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) U :=
  Functor.whiskerRight (spacesLocalizationComparison f V)
      (spacesRingedHom.relocalization c).toTopos.inverseImage ≫
    Functor.whiskerLeft ((spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((spacesEtalePullback f).obj V))
      (relocalizationInverseImageIso c).hom ≫
    Functor.whiskerLeft (spacesRingedToposHom f).toTopos.inverseImage
      (Functor.sheafPushforwardContinuousComp' (Over.mapForget c) (Type u)
        ((spacesEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V))
        (spacesEtaleTopology X)).hom

/-- Restricting the ambient sheaf and then relocalizing is restriction to the source slice. -/
def relocalizationOverIso {X : AlgebraicSpace S} {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (spacesEtaleTopology X).overPullback (Type u) V ⋙
        (spacesRingedHom.relocalization c).toTopos.inverseImage ≅
      (spacesEtaleTopology X).overPullback (Type u) U :=
  Functor.isoWhiskerLeft ((spacesEtaleTopology X).overPullback (Type u) V)
      (relocalizationInverseImageIso c) ≪≫
    Functor.sheafPushforwardContinuousComp' (Over.mapForget c) (Type u)
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) (spacesEtaleTopology X)

variable {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The spaces ambient comparison with both mk-object rebases included. -/
def rebasedSpacesComparison (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleTopology Y).overPullback (Type u) ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q)) ⋙
        (etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)) :=
  Functor.whiskerRight (relocalizationOverIso (smallEtaleInclusion_mkIso q).inv).hom
      ((spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
          (spacesEtalePullbackLift p g f q hcomm)).toTopos.inverseImage ⋙
        (etaleRelocalizeMkRelocalization_source p).toTopos.inverseImage) ≫
    Functor.whiskerRight
      (spacesAtComparison f (spacesEtaleSite.mk q) (spacesEtalePullbackLift p g f q hcomm))
      (etaleRelocalizeMkRelocalization_source p).toTopos.inverseImage ≫
    Functor.whiskerLeft (spacesRingedToposHom f).toTopos.inverseImage
      (relocalizationOverIso (smallEtaleInclusion_mkIso p).hom).hom

/-- The actual ambient comparison for the old small-site presentation. -/
def smallAmbientComparison (hcomm : p ≫ f = g ≫ q) :
    (smallEtaleTopology Y).overPullback (Type u) (smallEtaleSite.mk q) ⋙
        (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⟶
      (morphismOfTopoi f).inverseImage ⋙
        (smallEtaleTopology X).overPullback (Type u) (smallEtaleSite.mk p) :=
  Functor.whiskerRight (extensionOverIso Y (smallEtaleSite.mk q)).hom
      ((etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.inverseImage ⋙
        (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.inverseImage) ≫
    Functor.whiskerLeft (inclusionEquivalence Y).inverse
      (Functor.whiskerRight (rebasedSpacesComparison p g f q hcomm)
        (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.inverseImage) ≫
    Functor.whiskerLeft
      ((inclusionEquivalence Y).inverse ⋙ (spacesRingedToposHom f).toTopos.inverseImage)
      ((smallEtaleInclusion X).sheafPushforwardOverPostComp (smallEtaleSite.mk p) (Type u)).hom ≫
    Functor.whiskerRight (morphismInverseImageIso f).hom
      ((smallEtaleTopology X).overPullback (Type u) (smallEtaleSite.mk p))

/-- The old site's inverse image, transported by the concrete representable slice equivalences. -/
def slicePresentation (hcomm : p ≫ f = g ≫ q) :
    Over (etaleRepresentable (smallEtaleSite.mk q)) ⥤
      Over (etaleRepresentable (smallEtaleSite.mk p)) :=
  (etaleSliceEquivalence Y (smallEtaleSite.mk q)).inverse ⋙
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⋙
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor

/-- The canonical ambient comparison on slices of small-site sheaves. -/
def sliceAmbientComparison (hcomm : p ≫ f = g ≫ q) :
    Over.star (etaleRepresentable (smallEtaleSite.mk q)) ⋙ slicePresentation p g f q hcomm ⟶
      (morphismOfTopoi f).inverseImage ⋙ Over.star (etaleRepresentable (smallEtaleSite.mk p)) :=
  Functor.whiskerRight (SubcanonicalSlice.starInverseIso (smallEtaleTopology Y) (smallEtaleSite.mk q)).hom
      ((etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⋙
        (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor) ≫
    Functor.whiskerRight (smallAmbientComparison p g f q hcomm)
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor ≫
    Functor.whiskerLeft (morphismOfTopoi f).inverseImage
      (SubcanonicalSlice.restrictionIsoStar (smallEtaleTopology X) (smallEtaleSite.mk p)).hom

end AlgebraicGeometry.AlgebraicSpace.Relocalization
