/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-Isomorphism Localizers on Bounded-Below Termwise Models

This file keeps the bounded-below category as the ambient category.  It is the natural localizer
layer for functorial resolutions whose comparisons should remain morphisms of bounded-below
complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Plus

variable (A : Type u) [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- The inclusion of bounded-below complexes into all cochain complexes, regarded as a
morphism of quasi-isomorphism localizers. -/
@[stacks 05T6 "bounded-below inclusion as a localizer morphism"]
abbrev localizer :
    LocalizerMorphism (Plus.quasiIso A)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  LocalizerMorphism.ofEq rfl

namespace TermsIn

/-- The localizer morphism from termwise-`P` bounded-below complexes to all bounded-below
complexes. -/
@[stacks 05T6 "termwise bounded-below localizer morphism"]
abbrev localizerOnPlus (P : ObjectProperty A) :
    LocalizerMorphism
      (fullSubcategoryLocalizationSystem (Plus.termsIn P) (Plus.quasiIso A))
      (Plus.quasiIso A) :=
  fullSubcategoryLocalizerMorphism (Plus.termsIn P) (Plus.quasiIso A)

end TermsIn

end CochainComplex.Plus


