/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.twistedAlgebraPiece :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p) (n : ℤ),
      S.Modules)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedTwistPiece :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (n : ℤ),
      X.Modules)

#check
  (AlgebraicGeometry.Scheme.Hom.pulledBackTwistPiece :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p' : Y ⟶ S}
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (iso : X ≅ Y) (n : ℤ),
      X.Modules)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedAlgebraSection :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (n : ℤ) (U : S.Opensᵒᵖ),
      ModuleCat (S.presheaf.obj U))

#check
  (AlgebraicGeometry.Scheme.Hom.pulledBackTwistSection :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p' : Y ⟶ S}
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (iso : X ≅ Y) (n : ℤ) (U : X.Opensᵒᵖ),
      ModuleCat (X.presheaf.obj U))

#check
  (AlgebraicGeometry.Scheme.Hom.twistedTwistSection :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (n : ℤ) (U : X.Opensᵒᵖ),
      ModuleCat (X.presheaf.obj U))

#check
  (AlgebraicGeometry.Scheme.Hom.twistedAlgebraPieceOpenSections :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (n : ℤ) (V : S.Opens),
      AddCommGrpCat)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedAlgebraOpenSections :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (n : ℤ) (V : S.Opens),
      AddCommGrpCat)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedTwistFactorOpenSections :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (n : ℤ) (V : S.Opens),
      AddCommGrpCat)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedAlgebraPieceSectionMap :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (n : ℤ) (V : S.Opens),
      AlgebraicGeometry.Scheme.Hom.twistedAlgebraOpenSections L P n V ⟶
        AlgebraicGeometry.Scheme.Hom.twistedAlgebraPieceOpenSections L P n V)

#check
  (AlgebraicGeometry.Scheme.Hom.pulledBackTwistOpenSections :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (iso : X ≅ Y) (n : ℤ) (V : S.Opens),
      AddCommGrpCat)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedTwistOpenSections :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (n : ℤ) (V : S.Opens),
      AddCommGrpCat)

#check
  (AlgebraicGeometry.Scheme.Hom.twistedTwistFactorSectionMap :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (n : ℤ) (V : S.Opens),
      AlgebraicGeometry.Scheme.Hom.twistedTwistFactorOpenSections P L n V ⟶
        AlgebraicGeometry.Scheme.Hom.twistedTwistOpenSections P L n V)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      Type u)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist.sectionMap :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L)
      (V : S.Opens) (n : ℤ),
      AlgebraicGeometry.Scheme.Hom.twistedAlgebraOpenSections L P n V ⟶
        AlgebraicGeometry.Scheme.Hom.twistedTwistOpenSections P L n V)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist.algebraSectionMap :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L)
      (V : S.Opens) (n : ℤ),
      AlgebraicGeometry.Scheme.Hom.twistedAlgebraOpenSections L P n V ⟶
        AlgebraicGeometry.RingedSpace.moduleSectionsOnOpen (P'.algebra n) V)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist.algebraCompatibility_spec :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L),
      (∀ U : S.Opensᵒᵖ,
        ((((hTwist.algebraIso 0).hom.val.app U).hom) (hTwist.twistedOne U)) =
          P'.algebra.one U) ∧
        ∀ (U : S.Opensᵒᵖ) (n m : ℤ)
          (a : AlgebraicGeometry.Scheme.Hom.twistedAlgebraSection L P n U)
          (b : AlgebraicGeometry.Scheme.Hom.twistedAlgebraSection L P m U),
          ((((hTwist.algebraIso (n + m)).hom.val.app U).hom)
              (hTwist.twistedMul U n m a b)) =
            P'.algebra.mul U n m
              ((((hTwist.algebraIso n).hom.val.app U).hom) a)
              ((((hTwist.algebraIso m).hom.val.app U).hom) b))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L),
      Type u)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.compatibility_spec :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      {hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L}
      (hComparison :
        AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison P P' L hTwist),
      hComparison.iso.hom ≫ p' = p ∧
        (∀ (V : S.Opens) (n : ℤ),
          hTwist.algebraSectionMap V n ≫ hComparison.pullbackSectionMap V n ≫
              AlgebraicGeometry.RingedSpace.moduleSectionsMapOnOpen
                ((hComparison.theta n).hom) (p ⁻¹ᵁ V) =
            hTwist.sectionMap V n) ∧
          (∀ U : X.Opensᵒᵖ,
            ((((hComparison.theta 0).hom.val.app U).hom)
                (hComparison.pullbackOne U)) = hComparison.twistedOne U) ∧
            ∀ (U : X.Opensᵒᵖ) (n m : ℤ)
              (a : AlgebraicGeometry.Scheme.Hom.pulledBackTwistSection
                P' hComparison.iso n U)
              (b : AlgebraicGeometry.Scheme.Hom.pulledBackTwistSection
                P' hComparison.iso m U),
              ((((hComparison.theta (n + m)).hom.val.app U).hom)
                  (hComparison.pullbackMul U n m a b)) =
                hComparison.twistedMul U n m
                  ((((hComparison.theta n).hom.val.app U).hom) a)
                  ((((hComparison.theta m).hom.val.app U).hom) b))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.pulledBackTwistGraded :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p' : Y ⟶ S}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      (iso : X ≅ Y),
      CategoryTheory.GradedObject ℤ X.Modules)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.twistedTwistGraded :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L],
      CategoryTheory.GradedObject ℤ X.Modules)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.thetaGradedIso :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      {hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L}
      (hComparison :
        AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison P P' L hTwist),
      AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.pulledBackTwistGraded
          (P' := P') hComparison.iso ≅
        AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.twistedTwistGraded
          (P := P) (L := L))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.thetaGradedIso_hom_app :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p}
      {P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p'}
      {L : S.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
      {hTwist : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L}
      (hComparison :
        AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison P P' L hTwist)
      (n : ℤ),
      (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison.thetaGradedIso
          hComparison).hom n = (hComparison.theta n).hom)

/- Lemma 27.20.1: if two relative projective-spectrum presentations differ by twisting every
graded algebra piece by the corresponding integral tensor power of an invertible module, then
their relative projective spectra and twist families admit the compatible comparison. -/
@[stacks 02NC] #check
  (AlgebraicGeometry.Scheme.Hom.relativeProjPresentationTwistComparisonExists :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
      {p : X ⟶ S} {p' : Y ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (P' : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p')
      (L : S.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (hTwist :
        AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwist P P' L),
      ∃ hComparison :
          AlgebraicGeometry.Scheme.Hom.RelativeProjPresentationTwistComparison P P' L hTwist,
        hComparison.iso.hom ≫ p' = p ∧
          ∀ n : ℤ,
            Nonempty
              (AlgebraicGeometry.Scheme.Hom.pulledBackTwistPiece
                  P' hComparison.iso n ≅
                AlgebraicGeometry.Scheme.Hom.twistedTwistPiece P L n))
