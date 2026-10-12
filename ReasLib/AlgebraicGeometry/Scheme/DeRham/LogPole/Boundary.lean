/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.ResidueSequence
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FirstChern
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry RingedSite.Hom
open RingedSpace.DeRham.LogPole

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogPole

-- Local instance justification (defeq pin): localization and quotient terms must use the canonical derived category of the coefficient-module presentation used by the de Rham constructions.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): the restriction comparison uses the same specified coefficient pushforward and total-right-derived unit as CanonicalTensor.pushforward.
attribute [local instance] CanonicalTensor.coefficientPushforward_hasRightDerived

/-- The commutative square of schemes associated to `Y ⟶ X ⟶ S`. -/
theorem schemeSquare {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    CommSq i (i ≫ f) f (𝟙 S) := sorry

/-- Pushforward between the coefficient-module categories of the divisor square is exact. -/
theorem pushforward_exact {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    exactFunctor (RingedSpace.DeRham.Modules (i ≫ f).toLRSHom.toShHom)
      (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)
      (RingedSpace.DeRham.pushforward
        (RingedSpace.DeRham.LogPole.divisorSquare f i)) := sorry

/-- Coefficient-module pushforward along an effective Cartier divisor, bundled as an exact functor. -/
noncomputable def pushforwardExact {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    RingedSpace.DeRham.Modules (i ≫ f).toLRSHom.toShHom ⥤ₑ
      RingedSpace.DeRham.Modules f.toLRSHom.toShHom :=
  ⟨RingedSpace.DeRham.pushforward
      (RingedSpace.DeRham.LogPole.divisorSquare f i), pushforward_exact f i⟩

/-- The underlying functor of `pushforwardExact` is logarithmic coefficient pushforward. -/
theorem pushforwardExact_obj {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    (pushforwardExact f i).obj = RingedSpace.DeRham.pushforward
      (RingedSpace.DeRham.LogPole.divisorSquare f i) := sorry

/-- The relative de Rham complex of the divisor, derived-pushed to the ambient coefficient category. -/
noncomputable abbrev divisorObject {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :=
  (CanonicalTensor.pushforward (schemeSquare f i)).obj
    (Scheme.DeRham.DerivedPushforward.derivedComplex (i ≫ f))

/-- `divisorObject` is the canonical derived direct image of the divisor relative de Rham complex. -/
theorem divisorObject_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    divisorObject f i =
      (CanonicalTensor.pushforward (schemeSquare f i)).obj
        (Scheme.DeRham.DerivedPushforward.derivedComplex (i ≫ f)) := sorry

/-- The localization of the explicitly pushed divisor complex is canonically identified with the
total derived direct image used by class actions. -/
noncomputable def divisorComparison {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    DerivedCategory.Q.obj
        (RingedSpace.DeRham.LogPole.Canonical.divisorUnshiftedComplex f i) ≅
      divisorObject f i :=
  let K := RingedSpace.DeRham.LogPole.ordinaryComplex (i ≫ f)
  let F := (pushforwardExact f i).obj
  DerivedCategory.Q.mapIso (embeddingUpNat.mapAppIso F
      (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).symm ≪≫
    (F.mapDerivedCategoryFactors.app K).symm ≪≫
    F.mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso
        (RingedSpace.DeRham.Modules (i ≫ f).toLRSHom.toShHom)).app K).symm ≪≫
    (Functor.RightDerived.Exact.homotopyIso F).app
      (Scheme.DeRham.DerivedPushforward.derivedComplex (i ≫ f))

/-- `divisorComparison` is the composite of extension, exact-derived, localization, and
total-right-derived comparison isomorphisms. -/
theorem divisorComparison_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    divisorComparison f i =
      let K := RingedSpace.DeRham.LogPole.ordinaryComplex (i ≫ f)
      let F := (pushforwardExact f i).obj
      DerivedCategory.Q.mapIso (embeddingUpNat.mapAppIso F
          (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).symm ≪≫
        (F.mapDerivedCategoryFactors.app K).symm ≪≫
        F.mapDerivedCategory.mapIso
          ((DerivedCategory.quotientCompQhIso
            (RingedSpace.DeRham.Modules (i ≫ f).toLRSHom.toShHom)).app K).symm ≪≫
        (Functor.RightDerived.Exact.homotopyIso F).app
          (Scheme.DeRham.DerivedPushforward.derivedComplex (i ≫ f)) := sorry

/-- The canonical restriction from the ambient relative de Rham complex to the derived-pushed
relative de Rham complex of the divisor. -/
noncomputable def restriction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    Scheme.DeRham.DerivedPushforward.derivedComplex f ⟶ divisorObject f i :=
  Scheme.DeRham.Cohomology.derivedPullback (schemeSquare f i)

/-- The divisor restriction is the derived pullback attached to the canonical divisor square. -/
theorem restriction_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    restriction f i = Scheme.DeRham.Cohomology.derivedPullback (schemeSquare f i) := sorry

/-- The short exact residue sequence shifted by one degree. -/
noncomputable def shiftedSequence {S X Y : Scheme.{u}} {f : X ⟶ S} {i : Y ⟶ X}
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    ShortComplex (CochainComplex (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) ℤ) :=
  (shiftFunctor _ (1 : ℤ)).mapShortComplex.obj
    (RingedSpace.DeRham.LogPole.Canonical.canonicalSequence h_defined)

/-- The shifted logarithmic residue sequence is short exact. -/
theorem shiftedSequence_shortExact {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    (shiftedSequence h_defined).ShortExact := sorry

/-- The logarithmic residue boundary, normalized as a degree-two shifted morphism in the
ambient coefficient derived category. -/
noncomputable def boundary {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    ShiftedHom (divisorObject f i) (Scheme.DeRham.DerivedPushforward.derivedComplex f) (2 : ℤ) :=
  let U := RingedSpace.DeRham.LogPole.Canonical.divisorUnshiftedComplex f i
  let A := divisorObject f i
  let B := Scheme.DeRham.DerivedPushforward.derivedComplex f
  let eA : DerivedCategory.Q.obj U ≅ A := divisorComparison f i
  let K := RingedSpace.DeRham.LogPole.ordinaryComplex f
  let eB : B ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.quotientCompQhIso
      (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)).app K
  eA.inv ≫ DerivedCategory.Q.map (shiftNegShift U (1 : ℤ)).inv ≫
    DerivedCategory.triangleOfSESδ (shiftedSequence_shortExact f i h_defined) ≫
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧' ≫
    eB.inv⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) (1 : ℤ) (2 : ℤ) rfl).inv.app B

/-- The boundary is the degree-two transport of the connecting morphism of the shifted canonical
logarithmic residue sequence. -/
theorem boundary_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    boundary f i h_defined =
      let U := RingedSpace.DeRham.LogPole.Canonical.divisorUnshiftedComplex f i
      let A := divisorObject f i
      let B := Scheme.DeRham.DerivedPushforward.derivedComplex f
      let eA : DerivedCategory.Q.obj U ≅ A := divisorComparison f i
      let K := RingedSpace.DeRham.LogPole.ordinaryComplex f
      let eB : B ≅ DerivedCategory.Q.obj K :=
        (DerivedCategory.quotientCompQhIso
          (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)).app K
      eA.inv ≫ DerivedCategory.Q.map (shiftNegShift U (1 : ℤ)).inv ≫
        DerivedCategory.triangleOfSESδ (shiftedSequence_shortExact f i h_defined) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧' ≫
        eB.inv⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) (1 : ℤ) (2 : ℤ) rfl).inv.app B := rfl

/-- The Picard class of the negative divisor sheaf `𝒪_X(-Y)`. -/
noncomputable def negativeClass {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : X.PicardGroup :=
  Scheme.Modules.picardClass (RingedSpace.Hom.idealSheaf i.toShHom)

/-- The negative divisor class is represented by the ideal sheaf of `Y` in `X`. -/
theorem negativeClass_def {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    negativeClass i = Scheme.Modules.picardClass (RingedSpace.Hom.idealSheaf i.toShHom) := sorry

/-- The Picard class of the restriction `𝒪_X(-Y)|_Y`. -/
noncomputable def restrictedNegativeClass {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : Y.PicardGroup :=
  Scheme.Hom.picardPullback i (negativeClass i)

/-- The restricted negative-divisor class is the Picard pullback of `negativeClass`. -/
theorem restrictedNegativeClass_def {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    restrictedNegativeClass i = Scheme.Hom.picardPullback i (negativeClass i) := sorry

/-- The degree-two action of the canonical de Rham first Chern class of `𝒪_X(-Y)`. -/
noncomputable def negativeAction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    ShiftedHom (Scheme.DeRham.DerivedPushforward.derivedComplex f)
      (Scheme.DeRham.DerivedPushforward.derivedComplex f) (2 : ℤ) :=
  CanonicalAction.map f 2
    (Scheme.DeRham.firstChernClass f (RingedSpace.Hom.idealSheaf i.toShHom))

/-- The ambient negative-divisor action is the canonical first-Chern class action. -/
theorem negativeAction_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    negativeAction f i = CanonicalAction.map f 2
      (Scheme.DeRham.firstChernClass f (RingedSpace.Hom.idealSheaf i.toShHom)) := sorry

/-- The degree-two action of the first Chern class of the pulled-back ideal module, pushed to the
ambient coefficient category. -/
noncomputable def restrictedAction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    ShiftedHom (divisorObject f i) (divisorObject f i) (2 : ℤ) :=
  CanonicalAction.pushedMap (i ≫ f) (schemeSquare f i) 2
    (Scheme.DeRham.firstChernClass (i ≫ f)
      ((Scheme.Modules.pullback i).obj (RingedSpace.Hom.idealSheaf i.toShHom)))

/-- The pushed restricted action is the canonical action of the pulled-back ideal module. -/
theorem restrictedAction_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    restrictedAction f i = CanonicalAction.pushedMap (i ≫ f) (schemeSquare f i) 2
      (Scheme.DeRham.firstChernClass (i ≫ f)
        ((Scheme.Modules.pullback i).obj (RingedSpace.Hom.idealSheaf i.toShHom))) := rfl

/-- The upper triangle identity for the logarithmic residue boundary. -/
theorem upperTriangle {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    restriction f i ≫ boundary f i h_defined = negativeAction f i := sorry

/-- The lower triangle identity for the logarithmic residue boundary. -/
theorem lowerTriangle {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    boundary f i h_defined ≫ (shiftFunctor _ (2 : ℤ)).map (restriction f i) =
      restrictedAction f i := sorry

/-- The outer square obtained by composing the two triangle identities. -/
theorem classAction_commSq {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) :
    CommSq (negativeAction f i) (restriction f i)
      ((shiftFunctor _ (2 : ℤ)).map (restriction f i)) (restrictedAction f i) := sorry

end AlgebraicGeometry.Scheme.DeRham.LogPole
