/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for cospan equivalence constructors

This leaf contains the fine-grained evaluation and inverse-mate readouts used by transport and
bundled cospan code.  Keeping these equations separate lets constructor-only consumers avoid
loading the entire computation surface.
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

/-- The forward transformation of `equivalenceOfComponents` is the original transformation. -/
@[simp]
theorem equivalenceOfComponents.hom
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    (equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).hom = ψ := sorry

/-- The left component of the inverse of `equivalenceOfComponents` is the supplied inverse. -/
@[simp]
theorem equivalenceOfComponents.inv.left
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    left ((equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).inv) = leftEquiv.inv := sorry

/-- The right component of the inverse of `equivalenceOfComponents` is the supplied inverse. -/
@[simp]
theorem equivalenceOfComponents.inv.right
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    right ((equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).inv) = rightEquiv.inv := sorry

/-- The base component of the inverse of `equivalenceOfComponents` is the supplied inverse. -/
@[simp]
theorem equivalenceOfComponents.inv.base
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    base ((equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).inv) = baseEquiv.inv := sorry

/-- The left generating comparison of the inverse of `equivalenceOfComponents` is the mate
constructed by the generic pointwise-equivalence API. -/
@[simp]
theorem equivalenceOfComponents.inv.leftIso
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    leftIso ((equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).inv) =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
          leftHomIso rightHomIso baseHomIso)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm := sorry

/-- The right generating comparison of the inverse of `equivalenceOfComponents` is the mate
constructed by the generic pointwise-equivalence API. -/
@[simp]
theorem equivalenceOfComponents.inv.rightIso
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    rightIso ((equivalenceOfComponents ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso).inv) =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
          leftHomIso rightHomIso baseHomIso)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).symm := sorry

/-- The left component equivalence of `pointwiseEquivalenceMk` is the supplied one. -/
@[simp]
theorem pointwiseEquivalenceMk.app.left
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (pointwiseEquivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      leftEquiv := sorry

/-- The right component equivalence of `pointwiseEquivalenceMk` is the supplied one. -/
@[simp]
theorem pointwiseEquivalenceMk.app.right
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (pointwiseEquivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      rightEquiv := sorry

/-- The base component equivalence of `pointwiseEquivalenceMk` is the supplied one. -/
@[simp]
theorem pointwiseEquivalenceMk.app.base
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (pointwiseEquivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      baseEquiv := sorry

/-- The forward transformation of `equivalenceMk` is the transformation constructed by `mk`. -/
@[simp]
theorem equivalenceMk.hom
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      mk leftEquiv.hom rightEquiv.hom baseEquiv.hom leftIso rightIso := sorry

/-- Evaluation of `equivalenceMk` at the left vertex is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.app.left
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      leftEquiv := sorry

/-- Evaluation of `equivalenceMk` at the right vertex is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.app.right
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      rightEquiv := sorry

/-- Evaluation of `equivalenceMk` at the base vertex is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.app.base
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      baseEquiv := sorry

/-- The left component of the inverse of `equivalenceMk` is the supplied inverse. -/
@[simp]
theorem equivalenceMk.inv.left
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    left ((equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv) =
      leftEquiv.inv := sorry

/-- The right component of the inverse of `equivalenceMk` is the supplied inverse. -/
@[simp]
theorem equivalenceMk.inv.right
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    right ((equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv) =
      rightEquiv.inv := sorry

/-- The base component of the inverse of `equivalenceMk` is the supplied inverse. -/
@[simp]
theorem equivalenceMk.inv.base
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    base ((equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv) =
      baseEquiv.inv := sorry

/-- The left generating comparison of the inverse of `equivalenceMk` is the canonical mate. -/
@[simp]
theorem equivalenceMk.inv.leftIso
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    CategoryTheory.Bicategory.CospanTransform.leftIso
        ((equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv) =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (pointwiseEquivalenceMk
          leftEquiv rightEquiv baseEquiv leftIso rightIso)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm := sorry

/-- The right generating comparison of the inverse of `equivalenceMk` is the canonical mate. -/
@[simp]
theorem equivalenceMk.inv.rightIso
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    CategoryTheory.Bicategory.CospanTransform.rightIso
        ((equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv) =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (pointwiseEquivalenceMk
          leftEquiv rightEquiv baseEquiv leftIso rightIso)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).symm := sorry

/- Data audit (mathlib 4.32): these equations are proposition-valued readouts only. They expose
the forward transformation, endpoint components, and mate-generated inverse comparisons without
duplicating any cospan equivalence data. -/

end CategoryTheory.Bicategory.CospanTransform
