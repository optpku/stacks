/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-Isomorphism Localizers on Bounded-Above Termwise Models

This file keeps the bounded-above category as the ambient category.  It is the natural localizer
layer for functorial resolutions whose comparisons should remain morphisms of bounded-above
complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Minus

variable (A : Type u) [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- Quasi-isomorphisms of bounded-above complexes, detected on underlying cochain complexes. -/
@[stacks 05T7 "quasi-isomorphisms of bounded-above complexes"]
abbrev quasiIso : MorphismProperty (Minus A) :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage (Minus.ι A)

/-- The inclusion of bounded-above complexes into all cochain complexes, regarded as a
morphism of quasi-isomorphism localizers. -/
@[stacks 05T7 "bounded-above inclusion as a localizer morphism"]
abbrev localizer :
    LocalizerMorphism (Minus.quasiIso A)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  LocalizerMorphism.ofEq rfl

namespace TermsIn

/-- The localizer morphism from termwise-`P` bounded-above complexes to all bounded-above
complexes. -/
@[stacks 05T7 "termwise bounded-above localizer morphism"]
abbrev localizerOnMinus (P : ObjectProperty A) :
    LocalizerMorphism
      (fullSubcategoryLocalizationSystem (Minus.termsIn P) (Minus.quasiIso A))
      (Minus.quasiIso A) :=
  fullSubcategoryLocalizerMorphism (Minus.termsIn P) (Minus.quasiIso A)

end TermsIn

end CochainComplex.Minus


