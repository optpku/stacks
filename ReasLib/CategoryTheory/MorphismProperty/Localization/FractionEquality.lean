/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.List.TFAE

/-!
# Equality criteria for fractions with a fixed denominator

For an arbitrary localization model, equality of two fractions with a common denominator can be
tested either by an admissible refinement or by an arbitrary refinement whose composite with the
denominator is admissible. The left- and right-fraction statements are kept together as dual
facades over mathlib's canonical fraction types.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory
namespace MorphismProperty

namespace LeftFraction

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C}

/-- Lemma 4.27.6 (Stacks 04VF): for two left fractions with common denominator `s`, equality of
their images in any localization of `W` is equivalent both to equalizing their numerators by
postcomposition with a morphism in `W` and to equalizing them by a morphism `a` for which
`s ≫ a` lies in `W`. -/
@[stacks 04VF "left fraction equality with a fixed denominator"]
theorem map_mk_tfae
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    [ (LeftFraction.mk f s hs).map L (Localization.inverts L W) =
        (LeftFraction.mk g s hs).map L (Localization.inverts L W),
      ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t,
      ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a) ].TFAE := sorry
/- Proof strategy: cancel the common mapped denominator and apply
`MorphismProperty.map_eq_iff_postcomp L W`; multiplicativity gives the second-to-third
implication, while `LeftFraction.map_eq_iff` supplies the converse. -/

/-- Two left fractions with a common denominator have equal images exactly when their numerators
become equal after postcomposition by a morphism in `W`. -/
theorem map_mk_eq_iff_exists_postcomp
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (LeftFraction.mk f s hs).map L (Localization.inverts L W) =
        (LeftFraction.mk g s hs).map L (Localization.inverts L W) ↔
      ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t := sorry

/-- Two left fractions with a common denominator have equal images exactly when their numerators
become equal after postcomposition by a map whose composite with the denominator lies in `W`. -/
theorem map_mk_eq_iff_exists_postcomp_comp_mem
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (LeftFraction.mk f s hs).map L (Localization.inverts L W) =
        (LeftFraction.mk g s hs).map L (Localization.inverts L W) ↔
      ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a) := sorry

end LeftFraction

namespace RightFraction

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (S : MorphismProperty C)
  [L.IsLocalization S] [S.HasRightCalculusOfFractions]
variable {X X' Y : C}

/-- Lemma 4.27.14 (Stacks 04VJ): for two right fractions with common denominator `s`, equality of
their images in any localization of `S` is equivalent both to equalizing their numerators by
precomposition with a morphism in `S` and to equalizing them by a morphism `a` for which
`a ≫ s` lies in `S`. -/
@[stacks 04VJ "right fraction equality with a fixed denominator"]
theorem map_mk_tfae
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    [ (RightFraction.mk s hs f).map L (Localization.inverts L S) =
        (RightFraction.mk s hs g).map L (Localization.inverts L S),
      ∃ (X'' : C) (t : X'' ⟶ X'), S t ∧ t ≫ f = t ≫ g,
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) ].TFAE := sorry
/- Proof strategy: cancel the common mapped denominator and apply
`MorphismProperty.map_eq_iff_precomp L S`; multiplicativity gives the second-to-third
implication, while `RightFraction.map_eq_iff` supplies the converse. -/

/-- Two right fractions with a common denominator have equal images exactly when their numerators
become equal after precomposition by a morphism in `S`. -/
theorem map_mk_eq_iff_exists_precomp
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map L (Localization.inverts L S) =
        (RightFraction.mk s hs g).map L (Localization.inverts L S) ↔
      ∃ (X'' : C) (t : X'' ⟶ X'), S t ∧ t ≫ f = t ≫ g := sorry

/-- Two right fractions with a common denominator have equal images exactly when their numerators
become equal after precomposition by a map whose composite with the denominator lies in `S`. -/
theorem map_mk_eq_iff_exists_precomp_comp_mem
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map L (Localization.inverts L S) =
        (RightFraction.mk s hs g).map L (Localization.inverts L S) ↔
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) := sorry

end RightFraction

end MorphismProperty
end CategoryTheory
