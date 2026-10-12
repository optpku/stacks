/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

/-- The pullback map on Picard groups is injective when every base change has
an isomorphic pushforward of its structure sheaf. -/
theorem picardPullback_injective_of_structureSheafPushforward_iso
    {S : Scheme.{u}} (X : Over S)
    (h_structure : ∀ T : Over S,
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
        (pullback.fst T.hom X.hom).toShHom))
    (T : Over S) :
    Function.Injective (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)) := sorry

/-- A class maps to the basepoint of the sheafified relative Picard presheaf exactly
when it lies in the range of pullback from the base scheme. -/
theorem toSheafify_eq_basepoint_iff_mem_range_picardPullback
    {S : Scheme.{u}} (X : Over S)
    (h_structure : ∀ T : Over S,
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
        (pullback.fst T.hom X.hom).toShHom))
    (T : Over S) (L : (T ⊗ X).left.PicardGroup) :
    ((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T) L =
        ((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T)
          (0 : (T ⊗ X).left.PicardGroup) ↔
      L ∈ Set.range (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)) := sorry

/-- The Picard pullback along the base-changed section is a left inverse to
   pullback along the first projection of the base change. -/
theorem picardPullback_pullbackFst_leftInverse
    {S : Scheme.{u}} (X : Over S) (s : SplitEpi X.hom) (T : Over S) :
    Function.LeftInverse
      (Scheme.Hom.picardPullback ((s.pullbackFst T.hom).section_))
      (Scheme.Hom.picardPullback (pullback.fst T.hom X.hom)) := sorry

/-- The relative Picard sheafification map is surjective under the structure-sheaf
   hypothesis when the morphism admits a chosen split epimorphism. -/
theorem toSheafify_surjective_of_structureSheafPushforward_iso_of_splitEpi
    {S : Scheme.{u}} (X : Over S) (s : SplitEpi X.hom)
    (h_structure : ∀ U : Over S,
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
        (pullback.fst U.hom X.hom).toShHom))
    (T : Over S) :
    Function.Surjective
      (((Scheme.fppfTopology.over S).toSheafify (presheaf X)).app (op T)) := sorry

end AlgebraicGeometry.RelativePicard
