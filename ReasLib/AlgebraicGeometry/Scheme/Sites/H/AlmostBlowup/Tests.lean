/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Square
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup

/-!
# Test families for almost-blowup descent

This module records descent for the principal-center and two-generator
families of almost-blowup squares and relates these tests to sheafhood for a
chosen big h-site.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w uC vC

namespace AlgebraicGeometry

namespace AlmostBlowupDescent

/-- A presheaf satisfies principal-center descent when it sends every represented square
isomorphic to a canonical nilpotent principal-center square to a pullback square. -/
def IsPrincipalCenter {C : Type uC} [Category.{vC} C] (G : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : A) (J : Ideal A) (hJfg : J.FG)
      (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) (sq : Square C),
    (sq.map G ≅ (Spec.quotientMap_isAlmostBlowupSquare A f J hJfg hJ).square) →
      (sq.op.map F).IsPullback

/-- Principal-center descent is the quantified pullback condition for represented squares
isomorphic to canonical nilpotent principal-center squares. -/
theorem isPrincipalCenter_iff {C : Type uC} [Category.{vC} C] (G : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type w) :
    IsPrincipalCenter G F ↔
      ∀ (A : CommRingCat.{u}) (f : A) (J : Ideal A) (hJfg : J.FG)
          (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) (sq : Square C),
        (sq.map G ≅ (Spec.quotientMap_isAlmostBlowupSquare A f J hJfg hJ).square) →
          (sq.op.map F).IsPullback := Iff.rfl

/-- A presheaf satisfies two-generator descent when it sends every represented square
isomorphic to a canonical two-generator projective square to a pullback square. -/
def IsTwoGenerator {C : Type uC} [Category.{vC} C] (G : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : CommRingCat.{u}) (f₁ f₂ : A) (sq : Square C),
    (sq.map G ≅ (TwoGeneratorProj.toSpec_isAlmostBlowupSquare A f₁ f₂).square) →
      (sq.op.map F).IsPullback

/-- Two-generator descent is the quantified pullback condition for represented squares
isomorphic to canonical two-generator projective squares. -/
theorem isTwoGenerator_iff {C : Type uC} [Category.{vC} C] (G : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type w) :
    IsTwoGenerator G F ↔
      ∀ (A : CommRingCat.{u}) (f₁ f₂ : A) (sq : Square C),
        (sq.map G ≅ (TwoGeneratorProj.toSpec_isAlmostBlowupSquare A f₁ f₂).square) →
          (sq.op.map F).IsPullback := Iff.rfl

end AlmostBlowupDescent

namespace ChosenBigHSite.AlmostBlowup

/-- Zariski descent together with principal-center and two-generator descent implies
descent for every affine-base almost-blowup square on a chosen big h-site slice. -/
theorem isAffineDescent_of_examples
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (h_zariski : Presheaf.IsSheaf (bigZariskiTopology Schh S) F)
    (h_principal : AlmostBlowupDescent.IsPrincipalCenter
      (ChosenBigSite.sliceToScheme Schh S) F)
    (h_twoGenerator : AlmostBlowupDescent.IsTwoGenerator
      (ChosenBigSite.sliceToScheme Schh S) F) :
    IsAffineDescent Schh S F := sorry

end ChosenBigHSite.AlmostBlowup

namespace ChosenBigHSite.Sheaf

/-- A sheaf for the h topology satisfies descent for canonical nilpotent
principal-center almost-blowup squares. -/
theorem principalCenterDescentOfIsSheaf
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (bigTopology Schh S) F) :
    AlmostBlowupDescent.IsPrincipalCenter (ChosenBigSite.sliceToScheme Schh S) F := sorry

/-- A sheaf for the h topology satisfies descent for canonical two-generator
projective almost-blowup squares. -/
theorem twoGeneratorDescentOfIsSheaf
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (bigTopology Schh S) F) :
    AlmostBlowupDescent.IsTwoGenerator (ChosenBigSite.sliceToScheme Schh S) F := sorry

/-- Zariski descent, affine flat-proper-surjective equalizer descent,
principal-center descent, and two-generator descent imply the h-sheaf condition. -/
theorem ofExampleDescent
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (h_zariski : Presheaf.IsSheaf (bigZariskiTopology Schh S) F)
    (h_flatProper : Equalizer.IsAffineFlatProperSurjective Schh S F)
    (h_principal : AlmostBlowupDescent.IsPrincipalCenter
      (ChosenBigSite.sliceToScheme Schh S) F)
    (h_twoGenerator : AlmostBlowupDescent.IsTwoGenerator
      (ChosenBigSite.sliceToScheme Schh S) F) :
    Presheaf.IsSheaf (bigTopology Schh S) F := by
  exact ofZariskiAffineFlatProperAlmostBlowup Schh S F h_zariski h_flatProper
    (AlmostBlowup.isAffineDescent_of_examples Schh S F h_zariski h_principal h_twoGenerator)

/-- A type-valued presheaf on a chosen big h-site slice is an h-sheaf exactly when it
satisfies Zariski descent, affine flat-proper-surjective equalizer descent,
principal-center descent, and two-generator descent. -/
theorem iffZariskiAndFlatProperExampleDescent
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf (bigTopology Schh S) F ↔
      Presheaf.IsSheaf (bigZariskiTopology Schh S) F ∧
        Equalizer.IsAffineFlatProperSurjective Schh S F ∧
          AlmostBlowupDescent.IsPrincipalCenter
              (ChosenBigSite.sliceToScheme Schh S) F ∧
            AlmostBlowupDescent.IsTwoGenerator
              (ChosenBigSite.sliceToScheme Schh S) F := by
  constructor
  · intro hF
    exact ⟨zariskiOfIsSheaf Schh S F hF, affineFlatProperDescentOfIsSheaf Schh S F hF,
      principalCenterDescentOfIsSheaf Schh S F hF, twoGeneratorDescentOfIsSheaf Schh S F hF⟩
  · rintro ⟨h_zariski, h_flatProper, h_principal, h_twoGenerator⟩
    exact ofExampleDescent Schh S F h_zariski h_flatProper h_principal h_twoGenerator

end ChosenBigHSite.Sheaf

end AlgebraicGeometry
