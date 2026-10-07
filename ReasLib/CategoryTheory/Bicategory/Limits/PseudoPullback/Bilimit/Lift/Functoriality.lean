module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Identity and composition comparisons for pseudopullback lifts

Universal lifts between readable bilimit squares are canonical only up to invertible
`2`-morphism. This file specializes the shape-independent identity and composition comparisons
and records their images under the represented walking-cospan comparison.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The image of the identity apex map under the represented comparison is canonically the
readable cone itself. -/
noncomputable abbrev lift.id.comparisonIso (S : PseudoPullbackCone f g) :
    (S.toPseudoCone.comparison S.pt).obj (𝟙 S.pt) ≅ S.toPseudoCone.π :=
  PseudoCone.lift.id.comparisonIso S.toPseudoCone

/-- The represented comparison of two successive universal maps is canonically the source
readable cone. -/
noncomputable abbrev lift.comp.comparisonIso (R S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (T.toPseudoCone.comparison R.pt).obj (lift R S ≫ lift S T) ≅
      R.toPseudoCone.π :=
  PseudoCone.lift.comp.comparisonIso R.toPseudoCone S.toPseudoCone T.toPseudoCone

/-- The universal self-map of a bilimit pseudopullback apex is canonically isomorphic to its
identity map. -/
noncomputable abbrev lift.id.iso (S : PseudoPullbackCone f g) [S.IsBilimit] :
    𝟙 S.pt ≅ lift S S :=
  PseudoCone.lift.id.iso S.toPseudoCone

/-- Universal maps between three readable bilimit pseudopullback cones compose to the universal
map between their endpoints. -/
noncomputable abbrev lift.comp.iso (R S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    lift R S ≫ lift S T ≅ lift R T :=
  PseudoCone.lift.comp.iso R.toPseudoCone S.toPseudoCone T.toPseudoCone

/-- Mapping the forward universal identity cell through the represented comparison gives the
canonical identity-cone presentation. -/
@[simp]
theorem lift.id.iso.map_hom (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (S.toPseudoCone.comparison S.pt).map (lift.id.iso S).hom =
      (lift.id.comparisonIso S ≪≫
        (lift.comparisonIso S S).symm).hom := sorry

/-- Mapping the inverse universal identity cell gives the inverse canonical presentation. -/
@[simp]
theorem lift.id.iso.map_inv (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (S.toPseudoCone.comparison S.pt).map (lift.id.iso S).inv =
      (lift.id.comparisonIso S ≪≫
        (lift.comparisonIso S S).symm).inv := sorry

/-- Mapping the forward universal composition cell gives the canonical composite
presentation. -/
@[simp]
theorem lift.comp.iso.map_hom (R S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (T.toPseudoCone.comparison R.pt).map (lift.comp.iso R S T).hom =
      (lift.comp.comparisonIso R S T ≪≫
        (lift.comparisonIso R T).symm).hom := sorry

/-- Mapping the inverse universal composition cell gives the inverse canonical composite
presentation. -/
@[simp]
theorem lift.comp.iso.map_inv (R S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (T.toPseudoCone.comparison R.pt).map (lift.comp.iso R S T).inv =
      (lift.comp.comparisonIso R S T ≪≫
        (lift.comparisonIso R T).symm).inv := sorry

/- Data audit (mathlib 4.32): all non-`Prop` declarations are transparent walking-cospan
specializations of `PseudoCone.lift` functoriality. No additional universal map or coherence
choice is made at this presentation layer. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
