/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of bundled bicategorical cospans

This file is the readable `1`-morphism facade for the bicategory of bundled cospans. Its
morphisms remain the strong transformations supplied by the induced-bicategory construction;
the API only removes that wrapper and exposes the three vertex maps and two generating
comparison isomorphisms.

The corresponding `2`-morphism facade is layered in `Cospan.Bundled.Modification`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T U : Cospan B}

namespace Hom

/-- Forget the induced-bicategory wrapper on a morphism of bundled cospans. -/
abbrev toCospanTransform (ψ : S ⟶ T) :
    CospanTransform S.fst S.snd T.fst T.snd :=
  ψ.hom

/-- Regard a strong transformation between the canonical diagrams as a morphism of bundled
cospans. -/
def ofCospanTransform
    (ψ : CospanTransform S.fst S.snd T.fst T.snd) : S ⟶ T :=
  InducedBicategory.mkHom ψ

/-- Forgetting a lifted cospan transformation recovers the original transformation. -/
@[simp]
theorem ofCospanTransform.toCospanTransform
    (ψ : CospanTransform S.fst S.snd T.fst T.snd) :
    Hom.toCospanTransform (Hom.ofCospanTransform ψ) = ψ := sorry

/-- Lifting the underlying transformation of a bundled-cospan morphism recovers the
original morphism. -/
@[simp]
theorem toCospanTransform.ofCospanTransform (ψ : S ⟶ T) :
    Hom.ofCospanTransform (Hom.toCospanTransform ψ) = ψ := sorry

/-- Morphisms of bundled cospans are equivalent to strong transformations between their
canonical walking-cospan diagrams. -/
def homEquiv :
    (S ⟶ T) ≃ CospanTransform S.fst S.snd T.fst T.snd where
  toFun := toCospanTransform
  invFun := ofCospanTransform
  left_inv := toCospanTransform.ofCospanTransform
  right_inv := ofCospanTransform.toCospanTransform

/-- The forward map of `homEquiv` forgets the induced-bicategory wrapper. -/
@[simp]
theorem homEquiv_apply (ψ : S ⟶ T) :
    homEquiv ψ = toCospanTransform ψ := sorry

/-- The inverse map of `homEquiv` inserts the induced-bicategory wrapper. -/
@[simp]
theorem homEquiv_symm_apply
    (ψ : CospanTransform S.fst S.snd T.fst T.snd) :
    homEquiv.symm ψ = ofCospanTransform ψ := sorry

/-- The left-endpoint map of a morphism of bundled cospans. -/
abbrev left (ψ : S ⟶ T) : S.left ⟶ T.left :=
  CospanTransform.left (toCospanTransform ψ)

/-- The right-endpoint map of a morphism of bundled cospans. -/
abbrev right (ψ : S ⟶ T) : S.right ⟶ T.right :=
  CospanTransform.right (toCospanTransform ψ)

/-- The common-target map of a morphism of bundled cospans. -/
abbrev base (ψ : S ⟶ T) : S.base ⟶ T.base :=
  CospanTransform.base (toCospanTransform ψ)

/-- The generating comparison isomorphism along the left leg. -/
abbrev leftIso (ψ : S ⟶ T) :
    left ψ ≫ T.fst ≅ S.fst ≫ base ψ :=
  CospanTransform.leftIso (toCospanTransform ψ)

/-- The generating comparison isomorphism along the right leg. -/
abbrev rightIso (ψ : S ⟶ T) :
    right ψ ≫ T.snd ≅ S.snd ≫ base ψ :=
  CospanTransform.rightIso (toCospanTransform ψ)

/-- Construct a morphism of bundled cospans from its three vertex maps and two generating
comparison isomorphisms. -/
@[stacks 0040 "constructor for a morphism of bundled bicategorical cospans"]
def mk
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    S ⟶ T :=
  ofCospanTransform
    (CospanTransform.mk left right base leftIso rightIso)

/-- The left component of `mk` is the supplied map. -/
@[simp]
theorem mk_left
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    Hom.left (mk left right base leftIso rightIso) = left := sorry

/-- The right component of `mk` is the supplied map. -/
@[simp]
theorem mk_right
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    Hom.right (mk left right base leftIso rightIso) = right := sorry

/-- The common-target component of `mk` is the supplied map. -/
@[simp]
theorem mk_base
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    Hom.base (mk left right base leftIso rightIso) = base := sorry

/-- The left generating comparison of `mk` is the supplied isomorphism. -/
@[simp]
theorem mk_leftIso
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    Hom.leftIso (mk left right base leftIso rightIso) = leftIso := sorry

/-- The right generating comparison of `mk` is the supplied isomorphism. -/
@[simp]
theorem mk_rightIso
    (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (base : S.base ⟶ T.base)
    (leftIso : left ≫ T.fst ≅ S.fst ≫ base)
    (rightIso : right ≫ T.snd ≅ S.snd ≫ base) :
    Hom.rightIso (mk left right base leftIso rightIso) = rightIso := sorry

/-- Morphisms of bundled cospans are determined by their underlying strong transformations. -/
@[ext]
theorem ext
    (ψ φ : S ⟶ T)
    (transformEq : toCospanTransform ψ = toCospanTransform φ) :
    ψ = φ := sorry

/-- Reconstructing a bundled-cospan morphism from its five generator-level projections
recovers the original morphism. -/
@[simp]
theorem mk_components (ψ : S ⟶ T) :
    mk (left ψ) (right ψ) (base ψ) (leftIso ψ) (rightIso ψ) = ψ := sorry

/-- Forgetting an identity bundled-cospan morphism gives the canonical identity
transformation. -/
@[simp]
theorem toCospanTransform_id (S : Cospan B) :
    toCospanTransform (𝟙 S) =
      CospanTransform.id S.fst S.snd := sorry

/-- Forgetting a composite bundled-cospan morphism gives the composite of the underlying
transformations. -/
@[simp]
theorem toCospanTransform_comp (ψ : S ⟶ T) (φ : T ⟶ U) :
    toCospanTransform (ψ ≫ φ) =
      CospanTransform.comp (toCospanTransform ψ)
        (toCospanTransform φ) := sorry

/-- The left component of an identity bundled-cospan morphism is an identity. -/
@[simp]
theorem id_left (S : Cospan B) :
    left (𝟙 S) = 𝟙 S.left := sorry

/-- The right component of an identity bundled-cospan morphism is an identity. -/
@[simp]
theorem id_right (S : Cospan B) :
    right (𝟙 S) = 𝟙 S.right := sorry

/-- The common-target component of an identity bundled-cospan morphism is an identity. -/
@[simp]
theorem id_base (S : Cospan B) :
    base (𝟙 S) = 𝟙 S.base := sorry

/-- The left comparison of an identity bundled-cospan morphism is the canonical unitor
composite. -/
@[simp]
theorem id_leftIso (S : Cospan B) :
    leftIso (𝟙 S) = λ_ S.fst ≪≫ (ρ_ S.fst).symm := sorry

/-- The right comparison of an identity bundled-cospan morphism is the canonical unitor
composite. -/
@[simp]
theorem id_rightIso (S : Cospan B) :
    rightIso (𝟙 S) = λ_ S.snd ≪≫ (ρ_ S.snd).symm := sorry

/-- The left component of a composite bundled-cospan morphism is the composite of its left
components. -/
@[simp]
theorem comp_left (ψ : S ⟶ T) (φ : T ⟶ U) :
    left (ψ ≫ φ) = left ψ ≫ left φ := sorry

/-- The right component of a composite bundled-cospan morphism is the composite of its right
components. -/
@[simp]
theorem comp_right (ψ : S ⟶ T) (φ : T ⟶ U) :
    right (ψ ≫ φ) = right ψ ≫ right φ := sorry

/-- The common-target component of a composite bundled-cospan morphism is the composite of
its common-target components. -/
@[simp]
theorem comp_base (ψ : S ⟶ T) (φ : T ⟶ U) :
    base (ψ ≫ φ) = base ψ ≫ base φ := sorry

/-- The left comparison of a composite bundled-cospan morphism is the canonical pasting of
the two left comparisons. -/
@[simp]
theorem comp_leftIso (ψ : S ⟶ T) (φ : T ⟶ U) :
    leftIso (ψ ≫ φ) =
      α_ (left ψ) (left φ) U.fst ≪≫
        whiskerLeftIso (left ψ) (leftIso φ) ≪≫
        (α_ (left ψ) T.fst (base φ)).symm ≪≫
        whiskerRightIso (leftIso ψ) (base φ) ≪≫
        α_ S.fst (base ψ) (base φ) := sorry

/-- The right comparison of a composite bundled-cospan morphism is the canonical pasting of
the two right comparisons. -/
@[simp]
theorem comp_rightIso (ψ : S ⟶ T) (φ : T ⟶ U) :
    rightIso (ψ ≫ φ) =
      α_ (right ψ) (right φ) U.snd ≪≫
        whiskerLeftIso (right ψ) (rightIso φ) ≪≫
        (α_ (right ψ) T.snd (base φ)).symm ≪≫
        whiskerRightIso (rightIso ψ) (base φ) ≪≫
        α_ S.snd (base ψ) (base φ) := sorry

end Hom

/-- The cospan inclusion sends a bundled cospan to its canonical walking-cospan diagram. -/
@[simp]
theorem inclusion_obj (S : Cospan B) :
    (inclusion B).obj S = S.diagram := sorry

/-- The cospan inclusion forgets a bundled-cospan morphism to its underlying strong
transformation. -/
@[simp]
theorem inclusion_map {S T : Cospan B} (ψ : S ⟶ T) :
    (inclusion B).map ψ = Hom.toCospanTransform ψ := sorry

/- Data and axiom audit (mathlib 4.32):

`#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for
`ofCospanTransform`, `homEquiv`, and `mk`. Source inspection shows that they reuse the
induced-bicategory wrapper and canonical `CospanTransform.mk`, with all five generator-level
data explicit. Thus `sorryAx` is inherited from diagram/transformation coherence and wrapper
equalities and cannot choose a component or comparison. -/

end CategoryTheory.Bicategory.Cospan
