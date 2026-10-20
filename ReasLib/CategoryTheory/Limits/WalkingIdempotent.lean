/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# The walking idempotent

The one-object category of the multiplicative monoid `Bool` is the walking idempotent: `true` is
the identity and `false` is a freely distinguished idempotent.  Colimits of this shape detect
idempotent completeness.

For `Type`, this file gives an explicit colimit cocone whose vertex is the image of the
distinguished endomorphism.  Its carrier and structural maps are concrete; only functorial and
universal-property laws are deferred.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Limits

/-- The walking-idempotent category, implemented as the one-object category of the two-element
idempotent monoid `Bool`. -/
@[stacks 09P8 "walking-idempotent category"]
abbrev WalkingIdempotent := SingleObj Bool

namespace WalkingIdempotent

/-- The unique object of `WalkingIdempotent`. -/
abbrev star : WalkingIdempotent := SingleObj.star Bool

/-- The distinguished nonidentity idempotent endomorphism of `WalkingIdempotent`. -/
abbrev idem : End star := false

/-- The walking-idempotent category is filtered. -/
@[stacks 09P8 "finite filtered walking-idempotent category"]
instance isFiltered : IsFiltered WalkingIdempotent := sorry
/- Proof strategy: define `IsFiltered.cocone_objs` using `star` and identity maps, and define
`IsFiltered.cocone_maps` using `idem`; after `SingleObj.comp_as_mul`, the four Boolean cases are
equal because `false` is absorbing. The object `star` supplies nonemptiness. -/

/-- A category is idempotent complete exactly when it admits colimits of walking-idempotent
diagrams. -/
@[stacks 09P8 "idempotent completeness via walking-idempotent colimits"]
theorem isIdempotentComplete_iff_hasColimitsOfShape
    (C : Type u) [Category.{v} C] :
    IsIdempotentComplete C ↔ HasColimitsOfShape WalkingIdempotent C := sorry
/- Proof strategy: forward, split `M.map idem`; the retraction from `M.obj star` is the cocone leg,
and the section followed by an arbitrary cocone leg is its universal descent. Conversely, encode
an arbitrary idempotent `p : End X` as a walking-idempotent diagram. Its colimit leg `q : X ⟶ L`
and the descent `d : L ⟶ X` induced by the cocone with leg `p` satisfy `q ≫ d = p`; colimit
uniqueness and `p ≫ q = q` give `d ≫ q = 𝟙 L`. -/

variable (M : WalkingIdempotent ⥤ Type u)

/-- The image of the distinguished arrow under a walking-idempotent diagram is idempotent. -/
@[stacks 09P8 "diagram endomorphism attached to the idempotent arrow"]
theorem map_idem : M.map idem ≫ M.map idem = M.map idem := sorry
/- Proof strategy: rewrite the left side with `Functor.map_comp`, then use
`SingleObj.comp_as_mul` and `BooleanRing.mul_self false` to identify `idem ≫ idem` with `idem`. -/

/-- Naturality of the range factorization used in the image cocone. -/
theorem imageCocone_naturality (a : Bool) :
    M.map (a : End star) ≫ (Types.monoFactorisation (M.map idem)).e =
      (Types.monoFactorisation (M.map idem)).e ≫
        ((Functor.const WalkingIdempotent).obj (Types.Image (M.map idem))).map
          (X := star) (Y := star) (a : End star) := sorry
/- Proof strategy: split `a : Bool`; for `true`, use `M.map_id`, and for `false`, use
`map_idem M`. In both cases reduce the range-factorization map and the constant functor map. -/

/-- The cocone from a walking-idempotent diagram to the image of its distinguished
endomorphism. -/
def imageCocone : Cocone M where
  pt := Types.Image (M.map idem)
  ι := SingleObj.natTrans
    (Types.monoFactorisation (M.map idem)).e
    (imageCocone_naturality M)

/-- The vertex of the image cocone is the range of the distinguished idempotent. -/
@[simp]
theorem imageCocone_pt :
    (imageCocone M).pt = Types.Image (M.map idem) := sorry
/- Proof strategy: unfold `imageCocone`. -/

/-- The unique leg of the image cocone is the canonical range-factorization map. -/
@[simp]
theorem imageCocone_ι_app_star :
    (imageCocone M).ι.app star = (Types.monoFactorisation (M.map idem)).e := sorry
/- Proof strategy: unfold `imageCocone` and use the component formula for
`SingleObj.natTrans`. -/

/-- The explicit descent map from the image cocone to any other cocone. -/
def imageDesc (s : Cocone M) : Types.Image (M.map idem) ⟶ s.pt :=
  ↾fun x ↦ s.ι.app star x.1

/-- Evaluation of the explicit image descent map. -/
@[simp]
theorem imageDesc_apply (s : Cocone M) (x : Types.Image (M.map idem)) :
    imageDesc M s x = s.ι.app star x.1 := sorry
/- Proof strategy: unfold `imageDesc`. -/

/-- The image descent map factors the image cocone legs. -/
theorem imageDesc_fac (s : Cocone M) (j : WalkingIdempotent) :
    (imageCocone M).ι.app j ≫ imageDesc M s = s.ι.app j := sorry
/- Proof strategy: eliminate the unique object `j`, use the cocone relation `s.w idem`, and
evaluate the range-factorization map. The remaining pointwise equality says that a cocone leg is
constant along `M.map idem`. -/

/-- The image descent map is the unique map compatible with all cocone legs. -/
theorem imageDesc_uniq (s : Cocone M) (m : Types.Image (M.map idem) ⟶ s.pt)
    (hm : ∀ j, (imageCocone M).ι.app j ≫ m = s.ι.app j) :
    m = imageDesc M s := sorry
/- Proof strategy: use extensionality on the image subtype. Represent each image element as
`M.map idem x`, apply `hm` at `star`, and use `map_idem M`. -/

/-- The explicit image cocone is universal. Its descent morphism is concrete; only its laws are
supplied by the preceding proposition-valued helpers. -/
def imageIsColimit : IsColimit (imageCocone M) where
  desc := imageDesc M
  fac := imageDesc_fac M
  uniq := imageDesc_uniq M

/-- The colimit cocone of a `Type`-valued walking-idempotent diagram whose vertex is the image of
the distinguished idempotent. -/
@[stacks 09P8 "walking-idempotent colimit as the idempotent image"]
def imageColimitCocone : ColimitCocone M where
  cocone := imageCocone M
  isColimit := imageIsColimit M

/-- The canonical isomorphism from the abstract colimit to the image of `M.map idem`. -/
noncomputable def colimitIsoImage :
    colimit M ≅ Types.Image (M.map idem) :=
  colimit.isoColimitCocone (imageColimitCocone M)

/-- The canonical colimit comparison sends the unique colimit injection to the range
factorization of the distinguished idempotent. -/
@[simp]
theorem colimit_ι_comp_colimitIsoImage_hom :
    colimit.ι M star ≫ (colimitIsoImage M).hom =
      (Types.monoFactorisation (M.map idem)).e := sorry
/- Proof strategy: apply `colimit.isoColimitCocone_ι_hom` and unfold `imageColimitCocone`. -/

/-- The regular Bool action, whose distinguished endomorphism is the constant-false map. -/
def regularDiagram : WalkingIdempotent ⥤ Type :=
  SingleObj.functor
    ((TypeCat.endEquiv Bool).toMonoidHom.comp
      (MulAction.toEndHom : Bool →* Function.End Bool))

/-- The regular Bool-action diagram is a finite filtered colimit whose canonical map from its only
stage is not an isomorphism. -/
@[stacks 09P8 "finite filtered colimit not equal to its only stage"]
theorem regularDiagram_colimitι_not_isIso :
    ¬ IsIso (colimit.ι regularDiagram star) := sorry
/- Proof strategy: compose the colimit injection with `colimitIsoImage` and use
`colimit_ι_comp_colimitIsoImage_hom` to identify it with the range factorization of left
multiplication by `false`. That function sends both Boolean values to `false`, contradicting
bijectivity. -/

end WalkingIdempotent

end CategoryTheory.Limits
