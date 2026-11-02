/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for cospan pointwise equivalences

This leaf exposes the inverse, unit, and counit at each vertex of the walking cospan.  The
formulas are direct specializations of the generic `ofComponents` computation API and keep the
three endpoint roles visible to downstream users.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The left inverse component of `pointwiseEquivalence` is the supplied inverse. -/
@[simp]
theorem pointwiseEquivalence.left.inv
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).invApp
        (LocallyDiscrete.mk Limits.WalkingCospan.left) = leftEquiv.inv := by
  rfl

/-- The left unit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`leftHomIso`. -/
@[simp]
theorem pointwiseEquivalence.left.unit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).unit
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      Bicategory.Equivalence.OnHom.changeHom.unitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence leftEquiv)
        leftHomIso := by
  rfl

/-- The left counit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`leftHomIso`. -/
@[simp]
theorem pointwiseEquivalence.left.counit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).counit
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      Bicategory.Equivalence.OnHom.changeHom.counitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence leftEquiv)
        leftHomIso := by
  rfl

/-- The right inverse component of `pointwiseEquivalence` is the supplied inverse. -/
@[simp]
theorem pointwiseEquivalence.right.inv
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).invApp
        (LocallyDiscrete.mk Limits.WalkingCospan.right) = rightEquiv.inv := by
  rfl

/-- The right unit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`rightHomIso`. -/
@[simp]
theorem pointwiseEquivalence.right.unit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).unit
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      Bicategory.Equivalence.OnHom.changeHom.unitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence rightEquiv)
        rightHomIso := by
  rfl

/-- The right counit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`rightHomIso`. -/
@[simp]
theorem pointwiseEquivalence.right.counit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).counit
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      Bicategory.Equivalence.OnHom.changeHom.counitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence rightEquiv)
        rightHomIso := by
  rfl

/-- The base inverse component of `pointwiseEquivalence` is the supplied inverse. -/
@[simp]
theorem pointwiseEquivalence.base.inv
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).invApp
        (LocallyDiscrete.mk Limits.WalkingCospan.one) = baseEquiv.inv := by
  rfl

/-- The base unit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`baseHomIso`. -/
@[simp]
theorem pointwiseEquivalence.base.unit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).unit
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      Bicategory.Equivalence.OnHom.changeHom.unitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence baseEquiv)
        baseHomIso := by
  rfl

/-- The base counit of `pointwiseEquivalence` is obtained by changing the forward morphism along
`baseHomIso`. -/
@[simp]
theorem pointwiseEquivalence.base.counit
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).counit
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      Bicategory.Equivalence.OnHom.changeHom.counitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence baseEquiv)
        baseHomIso := by
  rfl

/- Data audit (mathlib 4.32): these readouts expose only the supplied vertex equivalences and
the canonical `changeHom` unit/counit cells. They add no new non-`Prop` data. -/

end CategoryTheory.Bicategory.CospanTransform
