/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.AlmostBlowup

/-!
# Descent criteria for sheaves on a chosen big h site

This module records affine flat-proper equalizer descent and affine almost
blowup descent, together with their characterization of type-valued sheaves on
a chosen big h-site slice.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigHSite

namespace Equalizer

/-- A presheaf satisfies equalizer descent for every flat, proper, surjective
morphism of finite presentation with affine represented target. -/
def IsAffineFlatProperSurjective (Schh : ChosenBigHSite.{u, v})
    (S : Schh.carrier) (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
      [IsAffine ((ChosenBigSite.sliceToScheme Schh S).obj U)]
      [Surjective ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [Flat ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [IsProper ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme Schh S).map f)],
    regularTopology.SingleEqualizerCondition F f

/-- Affine-target flat-proper-surjective equalizer descent is the corresponding
quantified condition on morphisms of a chosen big h-site slice. -/
theorem isAffineFlatProperSurjective_iff (Schh : ChosenBigHSite.{u, v})
    (S : Schh.carrier) (F : (Over S)ᵒᵖ ⥤ Type w) :
    IsAffineFlatProperSurjective Schh S F ↔
      ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
          [IsAffine ((ChosenBigSite.sliceToScheme Schh S).obj U)]
          [Surjective ((ChosenBigSite.sliceToScheme Schh S).map f)]
          [Flat ((ChosenBigSite.sliceToScheme Schh S).map f)]
          [IsProper ((ChosenBigSite.sliceToScheme Schh S).map f)]
          [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme Schh S).map f)],
        regularTopology.SingleEqualizerCondition F f := sorry

end Equalizer

namespace AlmostBlowup

/-- A presheaf satisfies affine almost-blowup descent when it sends every
almost blowup square with affine represented base to a pullback square. -/
def IsAffineDescent (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (sq : Square (Over S))
      [IsAffine ((ChosenBigSite.sliceToScheme Schh S).obj sq.X₄)]
      [IsClosedImmersion ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄)],
    (sq.map (ChosenBigSite.sliceToScheme Schh S)).IsPullback →
      IsAlmostBlowupSquare
        ((ChosenBigSite.sliceToScheme Schh S).map sq.f₂₄)
        ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄).ker →
      (sq.op.map F).IsPullback

/-- Affine almost-blowup descent is the corresponding pullback condition on
mapped squares, with the affine and almost-blowup hypotheses explicit. -/
theorem isAffineDescent_iff (Schh : ChosenBigHSite.{u, v})
    (S : Schh.carrier) (F : (Over S)ᵒᵖ ⥤ Type w) :
    IsAffineDescent Schh S F ↔
      ∀ (sq : Square (Over S))
          [IsAffine ((ChosenBigSite.sliceToScheme Schh S).obj sq.X₄)]
          [IsClosedImmersion ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄)],
        (sq.map (ChosenBigSite.sliceToScheme Schh S)).IsPullback →
          IsAlmostBlowupSquare
            ((ChosenBigSite.sliceToScheme Schh S).map sq.f₂₄)
            ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄).ker →
          (sq.op.map F).IsPullback := sorry

end AlmostBlowup

namespace Sheaf

/-- A sheaf for the h topology on a chosen big-site slice is a sheaf for the
restricted Zariski topology. -/
theorem zariskiOfIsSheaf (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (bigTopology Schh S) F) :
    Presheaf.IsSheaf (bigZariskiTopology Schh S) F := sorry

/-- A sheaf for the h topology has equalizer descent along every flat, proper,
surjective morphism of finite presentation with affine represented target. -/
theorem affineFlatProperDescentOfIsSheaf
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (bigTopology Schh S) F) :
    Equalizer.IsAffineFlatProperSurjective Schh S F := sorry

/-- A sheaf for the h topology sends every affine-base almost blowup square to
a pullback square of types. -/
theorem almostBlowupDescentOfIsSheaf
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (bigTopology Schh S) F) :
    AlmostBlowup.IsAffineDescent Schh S F := sorry

/-- Zariski descent, affine flat-proper-surjective equalizer descent, and
affine almost-blowup descent imply the sheaf condition for the h topology. -/
theorem ofZariskiAffineFlatProperAlmostBlowup
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (h_zariski : Presheaf.IsSheaf (bigZariskiTopology Schh S) F)
    (h_flatProper : Equalizer.IsAffineFlatProperSurjective Schh S F)
    (h_almostBlowup : AlmostBlowup.IsAffineDescent Schh S F) :
    Presheaf.IsSheaf (bigTopology Schh S) F := sorry

/-- A type-valued presheaf on a chosen big h-site slice is an h-sheaf exactly
when it satisfies Zariski descent, affine flat-proper-surjective equalizer
descent, and affine almost-blowup descent. -/
theorem iffZariskiAndFlatProperAlmostBlowup
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf (bigTopology Schh S) F ↔
      Presheaf.IsSheaf (bigZariskiTopology Schh S) F ∧
        Equalizer.IsAffineFlatProperSurjective Schh S F ∧
          AlmostBlowup.IsAffineDescent Schh S F := sorry

end Sheaf

end AlgebraicGeometry.ChosenBigHSite
