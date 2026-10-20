/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine

/-!
# Sheaf criteria on a chosen big h site

This module records the restricted Zariski topology and the proper-surjective
equalizer conditions used to recognize type-valued sheaves on a chosen big h
site.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigHSite

/-- The Zariski topology on a chosen big h-site slice, obtained by restricting
the Zariski topology on schemes along the represented-source functor. -/
def bigZariskiTopology (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (Over S) :=
  (ChosenBigSite.sliceToScheme X S).restrictedTopology Scheme.zariskiTopology

/-- The chosen big-slice Zariski topology is the restricted topology along the
represented-source functor. -/
theorem bigZariskiTopology_def (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    bigZariskiTopology X S =
      (ChosenBigSite.sliceToScheme X S).restrictedTopology Scheme.zariskiTopology := sorry

/-- Every Zariski covering of the chosen big-site slice is an h covering. -/
theorem bigZariskiTopology_le (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    bigZariskiTopology X S ≤ bigTopology X S := sorry

namespace Equalizer

/-- A presheaf satisfies descent for every proper, surjective morphism of
finite presentation in the chosen big h-site slice. -/
def IsProperSurjective (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
      [IsProper ((ChosenBigSite.sliceToScheme X S).map f)]
      [Surjective ((ChosenBigSite.sliceToScheme X S).map f)]
      [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme X S).map f)],
    regularTopology.SingleEqualizerCondition F f

/-- A presheaf satisfies proper-surjective finite-presentation descent when the
represented target is affine. -/
def IsAffineProperSurjective (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
      [IsAffine ((ChosenBigSite.sliceToScheme X S).obj U)]
      [IsProper ((ChosenBigSite.sliceToScheme X S).map f)]
      [Surjective ((ChosenBigSite.sliceToScheme X S).map f)]
      [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme X S).map f)],
    regularTopology.SingleEqualizerCondition F f

/-- Proper-surjective finite-presentation equalizer descent is equivalent to
the corresponding singleton-presieve sheaf condition. -/
theorem iffSheaf (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) :
    IsProperSurjective X S F ↔
      ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
          [IsProper ((ChosenBigSite.sliceToScheme X S).map f)]
          [Surjective ((ChosenBigSite.sliceToScheme X S).map f)]
          [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme X S).map f)],
        Presieve.IsSheafFor F (Presieve.singleton f) := sorry

/-- Affine-target proper-surjective finite-presentation equalizer descent is
equivalent to the corresponding singleton-presieve sheaf condition. -/
theorem iffAffineSheaf (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) :
    IsAffineProperSurjective X S F ↔
      ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
          [IsAffine ((ChosenBigSite.sliceToScheme X S).obj U)]
          [IsProper ((ChosenBigSite.sliceToScheme X S).map f)]
          [Surjective ((ChosenBigSite.sliceToScheme X S).map f)]
          [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme X S).map f)],
        Presieve.IsSheafFor F (Presieve.singleton f) := sorry

/-- Under the Zariski sheaf condition, proper-surjective finite-presentation
descent may be tested on affine represented targets. -/
theorem iffAffine (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w)
    (h_zariski : Presheaf.IsSheaf (bigZariskiTopology X S) F) :
    IsProperSurjective X S F ↔ IsAffineProperSurjective X S F := sorry

end Equalizer

namespace Sheaf

/-- A presheaf on a chosen big h-site slice is an h sheaf exactly when it is a
Zariski sheaf and satisfies proper-surjective finite-presentation equalizer
descent. -/
theorem iffZariskiAndEqualizer (X : ChosenBigHSite.{u, v}) (S : X.carrier)
    (F : (Over S)ᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf (bigTopology X S) F ↔
      Presheaf.IsSheaf (bigZariskiTopology X S) F ∧
        Equalizer.IsProperSurjective X S F := sorry

end Sheaf

end AlgebraicGeometry.ChosenBigHSite
