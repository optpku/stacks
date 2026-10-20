module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import ReasLib.AlgebraicGeometry.WLocalHull.Diagram

/-!
# Affine limits of finite vanishing-pattern spectra

The spectrum of the canonical w-localization is the inverse limit of the
finite-stage spectra. The closed-stage spectra have an affine inverse limit
with a canonical morphism to the spectrum of the w-localization.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry CommRingCat
open Algebra.WLocalHull

noncomputable section

universe u

namespace AlgebraicGeometry.WLocal.Construction

variable (A : Type u) [CommRing A]

/-- The bundled ring of the canonical w-localization. -/
def ring : CommRingCat.{u} :=
  CommRingCat.of (Algebra.WLocalHull.wLocalization A)

/-- The canonical ring homomorphism from a finite-stage algebra to the w-localization. -/
def ring_ι (E : Finset A) : (ringFunctor A).obj E ⟶ ring A :=
  ofHom (Algebra.WLocalHull.of A E)

/-- The canonical finite-stage maps form a cocone on the stage-ring diagram. -/
def ringCocone : Cocone (ringFunctor A) where
  pt := ring A
  ι.app := ring_ι A
  ι.naturality E F transition := by
    ext element
    exact Algebra.WLocalHull.of_stageMap A (leOfHom transition) element

/-- The canonical w-localization cocone is a colimit of the finite-stage rings. -/
def isColimit_ringCocone : IsColimit (ringCocone A) := by
  let stageHom (cocone : Cocone (ringFunctor A)) (E : Finset A) :
      stage A E →+* cocone.pt := (cocone.ι.app E).hom
  have compatible (cocone : Cocone (ringFunctor A)) :
      ∀ E F inclusion element,
        stageHom cocone F (stageMap A inclusion element) = stageHom cocone E element := by
    intro E F inclusion element
    exact congrArg (fun morphism ↦ morphism.hom element)
      (cocone.ι.naturality (homOfLE inclusion))
  refine ⟨(fun cocone ↦
    ofHom (Algebra.WLocalHull.lift A (stageHom cocone) (compatible cocone))), ?_, ?_⟩
  · intro cocone E
    apply CommRingCat.hom_ext
    change (Algebra.WLocalHull.lift A (stageHom cocone) (compatible cocone)).comp
      (Algebra.WLocalHull.of A E) = stageHom cocone E
    apply RingHom.ext
    intro element
    exact Algebra.WLocalHull.lift_of A (stageHom cocone) (compatible cocone) E element
  · intro cocone morphism compatibility
    apply CommRingCat.hom_ext
    apply Algebra.WLocalHull.hom_ext A
    intro E
    apply RingHom.ext
    intro element
    have stage_equality := congrArg (fun morphism ↦ morphism.hom element) (compatibility E)
    exact stage_equality.trans
      (Algebra.WLocalHull.lift_of A (stageHom cocone) (compatible cocone) E element).symm

/-- The spectrum of the w-localization carries the canonical cone on finite-stage spectra. -/
def schemeCone : Cone (schemeFunctor A) :=
  (Scheme.Spec.mapCone
    (ringCocone A).op).whisker
      (orderDualEquivalence (Finset A)).functor

/-- The affine scheme given by the spectrum of the canonical w-localization. -/
def scheme : Scheme.{u} :=
  (schemeCone A).pt

/-- The spectrum of the w-localization is the inverse limit of the finite-stage spectra. -/
def isLimit_schemeCone : IsLimit (schemeCone A) :=
  (isLimitOfPreserves Scheme.Spec
    (isColimit_ringCocone A).op).whiskerEquivalence
      (orderDualEquivalence (Finset A))

/-- The inverse diagram of finite-stage spectra admits a limit. -/
instance hasLimit_schemeFunctor : HasLimit (schemeFunctor A) :=
  HasLimit.mk ⟨schemeCone A, isLimit_schemeCone A⟩

/-- The spectrum of the w-localization is affine. -/
instance isAffine_scheme : IsAffine (scheme A) :=
  isAffine_Spec _

/-- The projection from the spectrum of the w-localization to a finite-stage spectrum. -/
def scheme_π (E : Finset A) : scheme A ⟶ spectrum A E :=
  (schemeCone A).π.app (OrderDual.toDual E)

/-- The colimit ring of the closed-stage algebras. -/
def closedRing : CommRingCat.{u} :=
  colimit (closedStageRingFunctor A)

/-- The canonical map from a closed-stage algebra to its colimit ring. -/
def closedRing_ι (E : Finset A) :
    (closedStageRingFunctor A).obj E ⟶ closedRing A :=
  colimit.ι (closedStageRingFunctor A) E

/-- The spectrum of the closed-stage colimit carries the canonical cone on closed-stage spectra. -/
def closedCone : Cone (closedFunctor A) :=
  (Scheme.Spec.mapCone
    (colimit.cocone (closedStageRingFunctor A)).op).whisker
        (orderDualEquivalence (Finset A)).functor

/-- The affine inverse limit of the finite closed-stage spectra. -/
def closedSubscheme : Scheme.{u} :=
  (closedCone A).pt

/-- The spectrum of the closed-stage colimit is the inverse limit of the closed-stage spectra. -/
def isLimit_closedCone : IsLimit (closedCone A) :=
  (isLimitOfPreserves Scheme.Spec
    (colimit.isColimit (closedStageRingFunctor A)).op).whiskerEquivalence
        (orderDualEquivalence (Finset A))

/-- The inverse diagram of closed-stage spectra admits a limit. -/
instance hasLimit_closedFunctor : HasLimit (closedFunctor A) :=
  HasLimit.mk ⟨closedCone A, isLimit_closedCone A⟩

/-- The inverse limit of closed-stage spectra is affine. -/
instance isAffine_closedSubscheme : IsAffine (closedSubscheme A) :=
  isAffine_Spec _

/-- The projection from the closed inverse limit to a finite closed-stage spectrum. -/
def closed_π (E : Finset A) :
    closedSubscheme A ⟶ Spec (CommRingCat.of (closedStage A E)) :=
  (closedCone A).π.app (OrderDual.toDual E)

/-- The morphism from the closed inverse limit to the spectrum of the w-localization,
induced by the finite-stage closed inclusions. -/
def closedι : closedSubscheme A ⟶ scheme A :=
  (isLimit_schemeCone A).lift ((Cone.postcompose (closedιNatTrans A)).obj (closedCone A))

/-- The canonical morphism from the closed inverse limit is a closed immersion. -/
instance isClosedImmersion_closedι : IsClosedImmersion (closedι A) := sorry

/-- The canonical inclusion commutes with the projections and finite-stage closed inclusions. -/
theorem closedι_comp_π (E : Finset A) :
    closedι A ≫ scheme_π A E = closed_π A E ≫ closedHom A E := sorry

end AlgebraicGeometry.WLocal.Construction
