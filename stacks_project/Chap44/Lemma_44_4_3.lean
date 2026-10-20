/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.ExactSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

/- Lemma 44.4.3 (1) -/
@[stacks 0B9N] #check
  (AlgebraicGeometry.RelativePicard.picardPullback_injective_of_structureSheafPushforward_iso :
    {S : Scheme.{u}} → (X : Over S) →
      (∀ T : Over S,
        IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
          (pullback.fst T.hom X.hom).toShHom)) →
      (T : Over S) →
      Function.Injective (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)))

/- Lemma 44.4.3 (2) -/
@[stacks 0B9N] #check
  (AlgebraicGeometry.RelativePicard.toSheafify_eq_basepoint_iff_mem_range_picardPullback :
    {S : Scheme.{u}} → (X : Over S) →
      (∀ T : Over S,
        IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
          (pullback.fst T.hom X.hom).toShHom)) →
      (T : Over S) → (L : (T ⊗ X).left.PicardGroup) →
      ((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T) L =
          ((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T)
            (0 : (T ⊗ X).left.PicardGroup) ↔
        L ∈ Set.range (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)))

/- Lemma 44.4.3 (3) -/
@[stacks 0B9N] #check
  (AlgebraicGeometry.RelativePicard.toSheafify_surjective_of_structureSheafPushforward_iso_of_splitEpi :
    {S : Scheme.{u}} → (X : Over S) → (s : SplitEpi X.hom) →
      (∀ U : Over S,
        IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
          (pullback.fst U.hom X.hom).toShHom)) →
      (T : Over S) →
      Function.Surjective
        (((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T)))

/- Lemma 44.4.3 (4) -/
@[stacks 0B9N] #check
  (AlgebraicGeometry.RelativePicard.picardPullback_pullbackFst_leftInverse :
    {S : Scheme.{u}} → (X : Over S) → (s : SplitEpi X.hom) → (T : Over S) →
      Function.LeftInverse
        (Scheme.Hom.picardPullback ((s.pullbackFst T.hom).section_))
        (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)))

end AlgebraicGeometry.RelativePicard
