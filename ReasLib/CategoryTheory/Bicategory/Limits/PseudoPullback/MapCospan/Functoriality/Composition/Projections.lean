module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Projection formulas for composition coherence of universal pseudopullback maps

The complete readable composite presentation determines a comparison isomorphism at every
walking-cospan vertex. Its left, right, and central specializations describe the complete
component behavior of a composite universal map.

These component isomorphisms provide the canonical conjugating cells for the projection
formulas of `mapCospan.comp.iso`. Downstream pullback and reindexing constructions can use
them without reopening the neutral pseudocone presentation.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z}
variable {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- The first-projection comparison carried by the complete presentation of a composite
universal map. -/
noncomputable abbrev mapCospan.comp.fstIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan S T ψ ≫ mapCospan T U φ) ≫ U.fst ≅
      S.fst ≫ (CospanTransform.comp ψ φ).left :=
  Pseudofunctor.StrongTrans.isoApp
    (mapCospan.comp.comparisonIso S T U ψ φ)
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The second-projection comparison carried by the complete presentation of a composite
universal map. -/
noncomputable abbrev mapCospan.comp.sndIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan S T ψ ≫ mapCospan T U φ) ≫ U.snd ≅
      S.snd ≫ (CospanTransform.comp ψ φ).right :=
  Pseudofunctor.StrongTrans.isoApp
    (mapCospan.comp.comparisonIso S T U ψ φ)
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The central comparison carried by the complete presentation of a composite universal map. -/
noncomputable abbrev mapCospan.comp.baseIso
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan S T ψ ≫ mapCospan T U φ) ≫ (U.fst ≫ f'') ≅
      (S.fst ≫ (CospanTransform.comp ψ φ).left) ≫ f'' :=
  Pseudofunctor.StrongTrans.isoApp
    (mapCospan.comp.comparisonIso S T U ψ φ)
    (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- At every walking-cospan vertex, the forward composition coherence is conjugated by
the composite presentation and the final universal comparison. -/
@[simp]
theorem mapCospan.comp.iso.map_hom_app
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'')
    (j : LocallyDiscrete Limits.WalkingCospan) :
    ((U.toPseudoCone.comparison S.pt).map
        (mapCospan.comp.iso S T U ψ φ).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapCospan.comp.comparisonIso S T U ψ φ) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapCospan.comparisonIso S U (CospanTransform.comp ψ φ)) j).inv := sorry

/-- At every walking-cospan vertex, the inverse composition coherence is conjugated by
the final universal comparison and the inverse composite presentation. -/
@[simp]
theorem mapCospan.comp.iso.map_inv_app
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'')
    (j : LocallyDiscrete Limits.WalkingCospan) :
    ((U.toPseudoCone.comparison S.pt).map
        (mapCospan.comp.iso S T U ψ φ).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapCospan.comparisonIso S U (CospanTransform.comp ψ φ)) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapCospan.comp.comparisonIso S T U ψ φ) j).inv := sorry

/-- The forward composition coherence commutes with the first projection, conjugated by
the composite and final first-projection comparisons. -/
@[simp]
theorem mapCospan.comp.iso.hom_fst
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).hom ▷ U.fst =
      (mapCospan.comp.fstIso S T U ψ φ).hom ≫
        (mapCospan.fstIso S U
          (CospanTransform.comp ψ φ)).inv := sorry

/-- The inverse composition coherence commutes with the first projection, conjugated by
the final and inverse composite first-projection comparisons. -/
@[simp]
theorem mapCospan.comp.iso.inv_fst
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).inv ▷ U.fst =
      (mapCospan.fstIso S U
          (CospanTransform.comp ψ φ)).hom ≫
        (mapCospan.comp.fstIso S T U ψ φ).inv := sorry

/-- The forward composition coherence commutes with the second projection, conjugated by
the composite and final second-projection comparisons. -/
@[simp]
theorem mapCospan.comp.iso.hom_snd
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).hom ▷ U.snd =
      (mapCospan.comp.sndIso S T U ψ φ).hom ≫
        (mapCospan.sndIso S U
          (CospanTransform.comp ψ φ)).inv := sorry

/-- The inverse composition coherence commutes with the second projection, conjugated by
the final and inverse composite second-projection comparisons. -/
@[simp]
theorem mapCospan.comp.iso.inv_snd
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).inv ▷ U.snd =
      (mapCospan.sndIso S U
          (CospanTransform.comp ψ φ)).hom ≫
        (mapCospan.comp.sndIso S T U ψ φ).inv := sorry

/-- The forward composition coherence commutes with the central leg, conjugated by the composite
and final central comparisons. -/
@[simp]
theorem mapCospan.comp.iso.hom_base
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).hom ▷ (U.fst ≫ f'') =
      (mapCospan.comp.baseIso S T U ψ φ).hom ≫
        (mapCospan.baseIso S U
          (CospanTransform.comp ψ φ)).inv := sorry

/-- The inverse composition coherence commutes with the central leg, conjugated by the final and
inverse composite central comparisons. -/
@[simp]
theorem mapCospan.comp.iso.inv_base
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g')
    (U : PseudoPullbackCone f'' g'')
    [T.IsBilimit] [U.IsBilimit]
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    (mapCospan.comp.iso S T U ψ φ).inv ▷ (U.fst ≫ f'') =
      (mapCospan.baseIso S U
          (CospanTransform.comp ψ φ)).hom ≫
        (mapCospan.comp.baseIso S T U ψ φ).inv := sorry

/- Data and axiom audit (mathlib 4.32):

The three vertex comparisons transparently evaluate the existing complete composite
presentation. All remaining declarations are equalities exposing components of the already
specified composition coherence. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
