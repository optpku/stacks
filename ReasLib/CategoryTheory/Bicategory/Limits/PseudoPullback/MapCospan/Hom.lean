/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Basic

/-!
# Cone morphisms induced by cospan transformations

This module packages the universal apex map and its complete comparison as a morphism from the
changed source cone to the bilimit target cone. It is the reusable structured form of
`mapCospan`; projection computations are kept in `MapCospan.Projections`.
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

/-- The canonical morphism from the source cone changed along a cospan transformation to a
bilimit target cone.

This packages `mapCospan` with its whole walking-cospan comparison, so downstream code can use
the ordinary `PseudoPullbackCone` morphism API without rebuilding `homMk`.
-/
@[stacks 02XA "morphism of pseudopullback cones induced by a cospan transformation"]
noncomputable def mapCospan.hom (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    S.changeCospan ψ ⟶ T :=
  lift.hom (S.changeCospan ψ) T

/-- The apex map of the canonical changed-cospan cone morphism is `mapCospan`. -/
@[simp]
theorem mapCospan.hom.map (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    PseudoPullbackCone.map (mapCospan.hom S T ψ) = mapCospan S T ψ := sorry

/-- The comparison modification of the canonical changed-cospan cone morphism is the forward
universal comparison. -/
@[simp]
theorem mapCospan.hom.fac (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    PseudoPullbackCone.fac (mapCospan.hom S T ψ) =
      (mapCospan.comparisonIso S T ψ).hom := sorry

/- Data audit (mathlib 4.32): `mapCospan.hom` reuses the canonical `lift.hom` of the changed
source cone. No second apex map or comparison modification is selected here. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
