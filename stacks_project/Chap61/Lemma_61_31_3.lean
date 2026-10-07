module

public import stacks_project.Chap61.Definition_61_12_8_Presentation
public import ReasLib.CategoryTheory.Sites.Topos.Retraction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.31.3

An inclusion of contained big pro-étale sites, given as a scheme-compatible
carrier functor that preserves chosen coverings, satisfies the Sites 7.21.8
hypotheses and induces a retraction of topoi. The same holds for the induced
slice inclusion over an object of the smaller site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry

noncomputable section

universe u v v' w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {Y : ChosenBigProetaleSite.{u, v'}}
variable (incl : X.carrier ⥤ Y.carrier)

/-- The carrier inclusion of contained big pro-étale presentations, recorded
together with scheme-compatibility and chosen-covering transport. -/
def containedInclusion (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    X.carrier ⥤ Y.carrier :=
  have := e
  have := hcov
  incl

/-- The recorded inclusion is the given carrier functor. -/
theorem containedInclusion_eq (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    containedInclusion incl e hcov = incl := sorry

/-- Lemma 61.31.3 (1): the inclusion of a contained big pro-étale site is full. -/
@[stacks 0F4S]
instance containedInclusion_full (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    (containedInclusion incl e hcov).Full := sorry

/-- Lemma 61.31.3 (2): the inclusion of a contained big pro-étale site is faithful. -/
@[stacks 0F4S]
instance containedInclusion_faithful (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    (containedInclusion incl e hcov).Faithful := sorry

/-- Lemma 61.31.3 (3): the inclusion is continuous for the chosen big pro-étale
topologies. -/
@[stacks 0F4S]
instance containedInclusion_isContinuous (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    (containedInclusion incl e hcov).IsContinuous X.toGrothendieck
      Y.toGrothendieck := sorry

/-- Lemma 61.31.3 (4): the inclusion is cocontinuous for the chosen big pro-étale
topologies. -/
@[stacks 0F4S]
instance containedInclusion_isCocontinuous (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    (containedInclusion incl e hcov).IsCocontinuous X.toGrothendieck
      Y.toGrothendieck := sorry

/-- Lemma 61.31.3 (5): the inclusion preserves fibre products. -/
@[stacks 0F4S]
instance containedInclusion_preservesPullbacks
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T)) :
    PreservesLimitsOfShape WalkingCospan (containedInclusion incl e hcov) :=
  sorry

/-- Sheaf pullback along the inclusion of a contained big pro-étale site
preserves finite limits. -/
instance containedInclusion_sheafPullback_preservesFiniteLimits
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    [HasWeakSheafify Y.toGrothendieck (Type w)]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((containedInclusion incl e hcov).sheafPullback (Type w)
        X.toGrothendieck Y.toGrothendieck) := sorry

/-- Lemma 61.31.3 (6): the continuous and cocontinuous morphisms of topoi induced
by the inclusion compose to the identity up to isomorphism on inverse images. -/
@[stacks 0F4S]
def containedInclusion_comp_inverseImageIso
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    [HasWeakSheafify Y.toGrothendieck (Type w)]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasLeftKanExtension P]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasPointwiseLeftKanExtension P]
    [HasSheafify X.toGrothendieck (Type w)]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((containedInclusion incl e hcov).morphismOfTopoiInOfContinuous
          X.toGrothendieck Y.toGrothendieck)
        ((containedInclusion incl e hcov).morphismOfTopoiInOfCocontinuous
          X.toGrothendieck Y.toGrothendieck)).inverseImage ≅
      (MorphismOfTopoiIn.id X.toGrothendieck).inverseImage :=
  Functor.Retraction.compInverseImageIso X.toGrothendieck Y.toGrothendieck
    (containedInclusion incl e hcov)

/-- The contained big-site retraction isomorphism is the Sites 7.21.8
inverse-image comparison. -/
theorem containedInclusion_comp_inverseImageIso_hom
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    [HasWeakSheafify Y.toGrothendieck (Type w)]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasLeftKanExtension P]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasPointwiseLeftKanExtension P]
    [HasSheafify X.toGrothendieck (Type w)]
    [∀ P : X.carrierᵒᵖ ⥤ Type w,
      (containedInclusion incl e hcov).op.HasPointwiseRightKanExtension P] :
    (containedInclusion_comp_inverseImageIso incl e hcov).hom =
      (Functor.Retraction.compInverseImageIso X.toGrothendieck Y.toGrothendieck
        (containedInclusion incl e hcov)).hom := sorry

/-- Lemma 61.31.3 (7): the induced slice inclusion is full. -/
@[stacks 0F4S]
instance containedSliceInclusion_full (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier) :
    (Over.post (containedInclusion incl e hcov) :
        Over S ⥤ Over ((containedInclusion incl e hcov).obj S)).Full := sorry

/-- Lemma 61.31.3 (8): the induced slice inclusion is faithful. -/
@[stacks 0F4S]
instance containedSliceInclusion_faithful (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier) :
    (Over.post (containedInclusion incl e hcov) :
        Over S ⥤ Over ((containedInclusion incl e hcov).obj S)).Faithful :=
  sorry

/-- Lemma 61.31.3 (9): the induced slice inclusion is continuous for the chosen
big pro-étale slice topologies. -/
@[stacks 0F4S]
instance containedSliceInclusion_isContinuous
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier) :
    (Over.post (containedInclusion incl e hcov)).IsContinuous (X.bigTopology S)
      (Y.bigTopology ((containedInclusion incl e hcov).obj S)) := sorry

/-- Lemma 61.31.3 (10): the induced slice inclusion is cocontinuous for the chosen
big pro-étale slice topologies. -/
@[stacks 0F4S]
instance containedSliceInclusion_isCocontinuous
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier) :
    (Over.post (containedInclusion incl e hcov)).IsCocontinuous (X.bigTopology S)
      (Y.bigTopology ((containedInclusion incl e hcov).obj S)) := sorry

/-- Lemma 61.31.3 (11): the induced slice inclusion preserves fibre products. -/
@[stacks 0F4S]
instance containedSliceInclusion_preservesPullbacks
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier) :
    PreservesLimitsOfShape WalkingCospan
      (Over.post (containedInclusion incl e hcov) :
        Over S ⥤ Over ((containedInclusion incl e hcov).obj S)) := sorry

/-- Sheaf pullback along the induced slice inclusion of contained big pro-étale
sites preserves finite limits. -/
instance containedSliceInclusion_sheafPullback_preservesFiniteLimits
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [HasWeakSheafify
      (Y.bigTopology ((containedInclusion incl e hcov).obj S)) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((Over.post (containedInclusion incl e hcov)).sheafPullback (Type w)
        (X.bigTopology S)
        (Y.bigTopology ((containedInclusion incl e hcov).obj S))) := sorry

/-- Lemma 61.31.3 (12): the continuous and cocontinuous morphisms of topoi induced
by the slice inclusion compose to the identity up to isomorphism on inverse
images. -/
@[stacks 0F4S]
def containedSliceInclusion_comp_inverseImageIso
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [HasWeakSheafify
      (Y.bigTopology ((containedInclusion incl e hcov).obj S)) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasLeftKanExtension P]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseLeftKanExtension
        P]
    [HasSheafify (X.bigTopology S) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P] :
    (MorphismOfTopoiIn.comp
        ((Over.post (containedInclusion incl e hcov)).morphismOfTopoiInOfContinuous
          (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S)))
        ((Over.post (containedInclusion incl e hcov)).morphismOfTopoiInOfCocontinuous
          (X.bigTopology S)
          (Y.bigTopology ((containedInclusion incl e hcov).obj S)))).inverseImage ≅
      (MorphismOfTopoiIn.id (X.bigTopology S)).inverseImage :=
  Functor.Retraction.compInverseImageIso (X.bigTopology S)
    (Y.bigTopology ((containedInclusion incl e hcov).obj S))
    (Over.post (containedInclusion incl e hcov))

/-- The contained slice-site retraction isomorphism is the Sites 7.21.8
inverse-image comparison on the induced slice functor. -/
theorem containedSliceInclusion_comp_inverseImageIso_hom
    (e : incl ⋙ Y.toScheme ≅ X.toScheme)
    (hcov : ∀ ⦃T : X.carrier⦄ ⦃R : Presieve T⦄,
      R ∈ X.pretopology.coverings T →
        R.map incl ∈ Y.pretopology.coverings (incl.obj T))
    (S : X.carrier)
    [HasWeakSheafify
      (Y.bigTopology ((containedInclusion incl e hcov).obj S)) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasLeftKanExtension P]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseLeftKanExtension
        P]
    [HasSheafify (X.bigTopology S) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (Over.post (containedInclusion incl e hcov)).op.HasPointwiseRightKanExtension
        P] :
    (containedSliceInclusion_comp_inverseImageIso incl e hcov S).hom =
      (Functor.Retraction.compInverseImageIso (X.bigTopology S)
        (Y.bigTopology ((containedInclusion incl e hcov).obj S))
        (Over.post (containedInclusion incl e hcov))).hom := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
