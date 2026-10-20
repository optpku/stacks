module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.ExactSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

/- Lemma 44.4.2 (1): if the structure sheaf of every base scheme is isomorphic to
   the pushforward of the structure sheaf after base change, then pullback from `T` to
   `T ⊗ X` is injective on Picard groups. -/
@[stacks 0B9M] #check
  (AlgebraicGeometry.RelativePicard.picardPullback_injective_of_structureSheafPushforward_iso :
    {S : Scheme.{u}} → (X : Over S) →
      (∀ T : Over S,
        IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
          (pullback.fst T.hom X.hom).toShHom)) →
      (T : Over S) →
      Function.Injective (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)))

/- Lemma 44.4.2 (2): under the same structure-sheaf hypothesis, a Picard class on
   `T ⊗ X` maps to the base point of `Pic_{X/S}(T)` exactly when it is pulled back
   from a Picard class on `T`. -/
@[stacks 0B9M] #check
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

end AlgebraicGeometry.RelativePicard
