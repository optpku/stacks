/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.FatPointPushout

/-!
# A non-reduced automorphism group

Two projective lines glued along three double points in characteristic two have finitely many
automorphisms over the base field, but their automorphisms are represented by a non-reduced scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Polynomial AlgebraicGeometry.FatPointPushout
open scoped AlgebraicGeometry DualNumber

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable (a b c : k) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)

/- Example 109.7.1 (Non-reduced automorphism group) (1):
the affine open is the image of the two affine branches. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.affineOpen_eq_range a b c hab hbc hca :
    (affineOpen a b c hab hbc hca : Set (scheme a b c hab hbc hca)) =
      Set.range (affineCoprodToScheme a b c hab hbc hca).base)

/- Example 109.7.1 (Non-reduced automorphism group) (2):
the indicated open is affine. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.affineOpen_isAffineOpen a b c hab hbc hca :
    IsAffineOpen (affineOpen a b c hab hbc hca))

/- Example 109.7.1 (Non-reduced automorphism group) (3):
sections on the affine open form the stated equalizer. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.sectionsToAffineCharts_isEqualizer a b c hab hbc hca :
    IsEqualizer (sectionsToAffineCharts a b c hab hbc hca)
      (CommRingCat.ofHom (equalizerLeft a b c))
      (CommRingCat.ofHom (equalizerRight a b c))
      (sectionsToAffineCharts_equalizes a b c hab hbc hca))

/- Example 109.7.1 (Non-reduced automorphism group) (4):
translation by ε is nontrivial. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.translation_ne_id (k := k) :
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom ≠
      AlgHom.id (DualNumber k) (Polynomial (DualNumber k)))

/- Example 109.7.1 (Non-reduced automorphism group) (5):
translation by ε is an involution. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.translation_comp_self (k := k) :
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.comp
        (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom =
      AlgHom.id (DualNumber k) (Polynomial (DualNumber k)))

/- Example 109.7.1 (Non-reduced automorphism group) (6):
translation on the three double points is an involution. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.quotientTranslationProd_comp_self a b c :
    (quotientTranslationProd a b c).comp (quotientTranslationProd a b c) =
      RingHom.id (doublePointRingDualNumber a × doublePointRingDualNumber b ×
        doublePointRingDualNumber c))

/- Example 109.7.1 (Non-reduced automorphism group) (7):
translation commutes with the first equalizer leg. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.equalizerLeftDualNumber_comp_translationProd a b c :
    (equalizerLeftDualNumber a b c).comp translationProd.toRingHom =
      (quotientTranslationProd a b c).comp (equalizerLeftDualNumber a b c))

/- Example 109.7.1 (Non-reduced automorphism group) (8):
translation commutes with the second equalizer leg. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.equalizerRightDualNumber_comp_translationProd a b c :
    (equalizerRightDualNumber a b c).comp translationProd.toRingHom =
      (quotientTranslationProd a b c).comp (equalizerRightDualNumber a b c))

/- Example 109.7.1 (Non-reduced automorphism group) (9):
translation on the equalizer agrees with simultaneous translation. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.translationEqualizer_subtype a b c :
    (equalizerDualNumber a b c).subtype.comp (translationEqualizer a b c) =
      translationProd.toRingHom.comp (equalizerDualNumber a b c).subtype)

/- Example 109.7.1 (Non-reduced automorphism group) (10):
translation on the equalizer is an involution. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.translationEqualizer_comp_self a b c :
    (translationEqualizer a b c).comp (translationEqualizer a b c) =
      RingHom.id (equalizerDualNumber a b c))

/- Example 109.7.1 (Non-reduced automorphism group) (11):
translation on the equalizer is nontrivial. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.translationEqualizer_ne_id a b c :
    translationEqualizer a b c ≠ RingHom.id (equalizerDualNumber a b c))

/- Example 109.7.1 (Non-reduced automorphism group) (12):
translation extends to an automorphism over the dual numbers. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.existsAutOverDualNumber a b c hab hbc hca :
    ∃ φ : Aut (schemeOverDualNumber a b c hab hbc hca),
      affineChartLeftDualNumber a b c hab hbc hca ≫ φ.hom.left =
          translationSpec ≫ affineChartLeftDualNumber a b c hab hbc hca ∧
        affineChartRightDualNumber a b c hab hbc hca ≫ φ.hom.left =
          translationSpec ≫ affineChartRightDualNumber a b c hab hbc hca)

/- Example 109.7.1 (Non-reduced automorphism group) (13):
the automorphism group over the base field is finite. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.autFinite a b c hab hbc hca :
    Finite (Aut (schemeOver a b c hab hbc hca)))

/- Example 109.7.1 (Non-reduced automorphism group) (14):
base change does not exhaust the dual-number automorphisms. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.autRestriction_not_surjective a b c hab hbc hca :
    ¬ Function.Surjective (autRestriction a b c hab hbc hca))

/- Example 109.7.1 (Non-reduced automorphism group) (15):
the automorphism family is represented by a non-reduced scheme. -/
@[stacks 0DSU] #check (AlgebraicGeometry.FatPointPushout.existsNonreducedAutScheme a b c hab hbc hca :
    ∃ (G : SchemeOverField k)
      (α : Aut ((Over.pullback G.hom).obj (schemeOver a b c hab hbc hca))),
      SchemeOverField.Automorphism.IsUniversalFamily (schemeOver a b c hab hbc hca) α ∧
        ¬ IsReduced G.left)
