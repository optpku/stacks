/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms between K-flat complexes

@stack 0FPB

Restricting quasi-isomorphisms to the full subcategory of K-flat homotopy objects gives the
denominator system used for K-flat localization. K-flat resolution hypotheses are expressed
using the canonical `LocalizerMorphism.HasLeftResolutions` interface rather than a parallel
witness package. Tensor compatibility is isolated in the `KFlat.QuasiIso.Monoidal` leaf.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory.KFlat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [CategoryWithHomology C]

/-- Quasi-isomorphisms restricted to the full subcategory of K-flat homotopy objects. -/
@[stacks 0FPB "K-flat quasi-isomorphisms"]
abbrev quasiIso : MorphismProperty (KFlat C) :=
  fullSubcategoryLocalizationSystem (kFlat C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The canonical resolution condition saying that every homotopy object receives a
quasi-isomorphism from a K-flat object. -/
@[stacks 0FPB "K-flat resolutions"]
abbrev HasResolutions (C : Type u) [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [CategoryWithHomology C] : Prop :=
  (fullSubcategoryLocalizerMorphism (kFlat C)
    (HomotopyCategory.quasiIso C (up ℤ))).HasLeftResolutions

/-- Every homotopy object admits a quasi-isomorphism from a K-flat object when K-flat
resolutions exist. -/
@[stacks 0FPB "existence of K-flat resolution morphisms"]
theorem exists_quasiIso [HasResolutions C] (K : HomotopyCategory C (up ℤ)) :
    ∃ P : KFlat C, ∃ f : P.obj ⟶ K, HomotopyCategory.quasiIso C (up ℤ) f := sorry

end CategoryTheory.HomotopyCategory.KFlat
