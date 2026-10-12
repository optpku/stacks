/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms between K-flat termwise-flat models

@stack 06YY
@stack 06YS

This localization leaf restricts homotopy quasi-isomorphisms to the full subcategory of
K-flat objects represented by termwise-flat complexes.  The underlying object property remains
available independently of localization and resolution infrastructure.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat

variable (C : Type u) [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [CategoryWithHomology C]

/-- Quasi-isomorphisms restricted to K-flat homotopy objects with flat terms. -/
@[stacks 06YY "good quasi-isomorphisms"]
abbrev quasiIso : MorphismProperty (TermwiseFlat C) :=
  fullSubcategoryLocalizationSystem (termwiseFlat C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The canonical condition that every homotopy object has a quasi-isomorphic K-flat
representative with flat terms. -/
@[stacks 06YS "K-flat termwise-flat resolutions"]
abbrev HasResolutions : Prop :=
  (fullSubcategoryLocalizerMorphism (termwiseFlat C)
    (HomotopyCategory.quasiIso C (up ℤ))).HasLeftResolutions

end CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat
