/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan

/-!
# Universal maps induced by cospan transformations

This module owns the semantic universal apex map induced by a cospan transformation and its
complete walking-cospan comparison.  The data-level transport of cones is kept in
`PseudoPullback.ChangeCospan`; this is the first layer that requires a bilimit target.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The apex morphism induced by a cospan transformation and a bilimit target cone.

This is the bicategorical semantic analogue of `CategoricalPullback.map`; concrete selected
pseudopullback models may additionally identify a computational implementation with this
universal map.
-/
noncomputable def mapCospan (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    S.pt ⟶ T.pt :=
  lift (S.changeCospan ψ) T

/-- The complete walking-cospan comparison carried by the universal map induced by a cospan
transformation.
-/
noncomputable abbrev mapCospan.comparisonIso (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (T.toPseudoCone.comparison S.pt).obj (mapCospan S T ψ) ≅
      (S.changeCospan ψ).toPseudoCone.π :=
  lift.comparisonIso (S.changeCospan ψ) T

/- Data audit (mathlib 4.32): `mapCospan` and `mapCospan.comparisonIso` delegate all non-`Prop`
content to the single shape-independent lift owner.  Their `sorryAx` dependencies are confined
to inherited universal-property and coherence proof fields. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
