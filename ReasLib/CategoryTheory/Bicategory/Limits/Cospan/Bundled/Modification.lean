/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modifications of bundled bicategorical cospans

This file is the readable `2`-morphism facade for the induced bicategory of bundled cospans.
It identifies a bundled `2`-morphism with the underlying modification of canonical
walking-cospan transformations and exposes its three vertex cells and two generating
naturality squares.

Whiskering, associator, and unitor computations are layered in `Cospan.Bundled.Coherence`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

namespace Hom₂

variable {ψ φ χ : S ⟶ T}

/-- Forget the induced-bicategory wrapper on a `2`-morphism of bundled cospans. -/
abbrev toModification (Γ : ψ ⟶ φ) :
    Pseudofunctor.StrongTrans.Hom
      (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ) :=
  Γ.hom

/-- Regard a modification between the underlying cospan transformations as a `2`-morphism
of bundled cospans. -/
def ofModification
    (Γ : Pseudofunctor.StrongTrans.Hom
      (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ)) :
    ψ ⟶ φ :=
  InducedBicategory.mkHom₂ Γ

/-- Forgetting a lifted cospan modification recovers the original modification. -/
@[simp]
theorem toModification_ofModification
    (Γ : Pseudofunctor.StrongTrans.Hom
      (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ)) :
    toModification (ofModification Γ) = Γ := sorry

/-- Lifting the underlying modification of a bundled-cospan `2`-morphism recovers the
original `2`-morphism. -/
@[simp]
theorem ofModification_toModification (Γ : ψ ⟶ φ) :
    ofModification (toModification Γ) = Γ := sorry

/-- Bundled-cospan `2`-morphisms are equivalent to modifications between their underlying
canonical cospan transformations. -/
def modificationEquiv :
    (ψ ⟶ φ) ≃
      Pseudofunctor.StrongTrans.Hom
        (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ) where
  toFun := toModification
  invFun := ofModification
  left_inv := ofModification_toModification
  right_inv := toModification_ofModification

/-- The forward map of `modificationEquiv` forgets the induced-bicategory wrapper. -/
@[simp]
theorem modificationEquiv_apply (Γ : ψ ⟶ φ) :
    modificationEquiv Γ = toModification Γ := sorry

/-- The inverse map of `modificationEquiv` inserts the induced-bicategory wrapper. -/
@[simp]
theorem modificationEquiv_symm_apply
    (Γ : Pseudofunctor.StrongTrans.Hom
      (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ)) :
    modificationEquiv.symm Γ = ofModification Γ := sorry

/-- The left-endpoint cell of a `2`-morphism of bundled cospans. -/
abbrev left (Γ : ψ ⟶ φ) : Hom.left ψ ⟶ Hom.left φ :=
  CospanTransform.Hom.left (toModification Γ)

/-- The right-endpoint cell of a `2`-morphism of bundled cospans. -/
abbrev right (Γ : ψ ⟶ φ) : Hom.right ψ ⟶ Hom.right φ :=
  CospanTransform.Hom.right (toModification Γ)

/-- The common-target cell of a `2`-morphism of bundled cospans. -/
abbrev base (Γ : ψ ⟶ φ) : Hom.base ψ ⟶ Hom.base φ :=
  CospanTransform.Hom.base (toModification Γ)

/-- Naturality of a bundled-cospan `2`-morphism on the left generating arrow. -/
@[reassoc]
theorem left_naturality (Γ : ψ ⟶ φ) :
    left Γ ▷ T.fst ≫ (Hom.leftIso φ).hom =
      (Hom.leftIso ψ).hom ≫ S.fst ◁ base Γ := sorry

/-- Naturality on the left generating arrow, solved in the inverse orientation. -/
@[reassoc]
theorem left_naturality_inv (Γ : ψ ⟶ φ) :
    (Hom.leftIso ψ).inv ≫ left Γ ▷ T.fst =
      S.fst ◁ base Γ ≫ (Hom.leftIso φ).inv := sorry

/-- Naturality of a bundled-cospan `2`-morphism on the right generating arrow. -/
@[reassoc]
theorem right_naturality (Γ : ψ ⟶ φ) :
    right Γ ▷ T.snd ≫ (Hom.rightIso φ).hom =
      (Hom.rightIso ψ).hom ≫ S.snd ◁ base Γ := sorry

/-- Naturality on the right generating arrow, solved in the inverse orientation. -/
@[reassoc]
theorem right_naturality_inv (Γ : ψ ⟶ φ) :
    (Hom.rightIso ψ).inv ≫ right Γ ▷ T.snd =
      S.snd ◁ base Γ ≫ (Hom.rightIso φ).inv := sorry

/-- Construct a bundled-cospan `2`-morphism from its three vertex cells and the two
generating naturality squares. -/
@[stacks 0040 "constructor for a 2-morphism of bundled bicategorical cospans"]
def mk
    (left : Hom.left ψ ⟶ Hom.left φ)
    (right : Hom.right ψ ⟶ Hom.right φ)
    (base : Hom.base ψ ⟶ Hom.base φ)
    (leftNaturality :
      left ▷ T.fst ≫ (Hom.leftIso φ).hom =
        (Hom.leftIso ψ).hom ≫ S.fst ◁ base)
    (rightNaturality :
      right ▷ T.snd ≫ (Hom.rightIso φ).hom =
        (Hom.rightIso ψ).hom ≫ S.snd ◁ base) :
    ψ ⟶ φ :=
  ofModification
    (CospanTransform.Hom.mk left right base
      leftNaturality rightNaturality)

/-- The left component of `mk` is the supplied cell. -/
@[simp]
theorem mk_left
    (left : Hom.left ψ ⟶ Hom.left φ)
    (right : Hom.right ψ ⟶ Hom.right φ)
    (base : Hom.base ψ ⟶ Hom.base φ)
    (leftNaturality :
      left ▷ T.fst ≫ (Hom.leftIso φ).hom =
        (Hom.leftIso ψ).hom ≫ S.fst ◁ base)
    (rightNaturality :
      right ▷ T.snd ≫ (Hom.rightIso φ).hom =
        (Hom.rightIso ψ).hom ≫ S.snd ◁ base) :
    Hom₂.left (mk left right base leftNaturality rightNaturality) = left := sorry

/-- The right component of `mk` is the supplied cell. -/
@[simp]
theorem mk_right
    (left : Hom.left ψ ⟶ Hom.left φ)
    (right : Hom.right ψ ⟶ Hom.right φ)
    (base : Hom.base ψ ⟶ Hom.base φ)
    (leftNaturality :
      left ▷ T.fst ≫ (Hom.leftIso φ).hom =
        (Hom.leftIso ψ).hom ≫ S.fst ◁ base)
    (rightNaturality :
      right ▷ T.snd ≫ (Hom.rightIso φ).hom =
        (Hom.rightIso ψ).hom ≫ S.snd ◁ base) :
    Hom₂.right (mk left right base leftNaturality rightNaturality) = right := sorry

/-- The common-target component of `mk` is the supplied cell. -/
@[simp]
theorem mk_base
    (left : Hom.left ψ ⟶ Hom.left φ)
    (right : Hom.right ψ ⟶ Hom.right φ)
    (base : Hom.base ψ ⟶ Hom.base φ)
    (leftNaturality :
      left ▷ T.fst ≫ (Hom.leftIso φ).hom =
        (Hom.leftIso ψ).hom ≫ S.fst ◁ base)
    (rightNaturality :
      right ▷ T.snd ≫ (Hom.rightIso φ).hom =
        (Hom.rightIso ψ).hom ≫ S.snd ◁ base) :
    Hom₂.base (mk left right base leftNaturality rightNaturality) = base := sorry

/-- Bundled-cospan `2`-morphisms are determined by their three vertex cells. -/
@[ext]
theorem ext
    (Γ Δ : ψ ⟶ φ)
    (leftEq : left Γ = left Δ) (rightEq : right Γ = right Δ)
    (baseEq : base Γ = base Δ) :
    Γ = Δ := sorry

/-- Reconstructing a bundled-cospan `2`-morphism from its component API recovers the original
`2`-morphism. -/
@[simp]
theorem mk_components (Γ : ψ ⟶ φ) :
    mk (left Γ) (right Γ) (base Γ)
      (left_naturality Γ) (right_naturality Γ) = Γ := sorry

/-- Forgetting an identity bundled-cospan `2`-morphism gives the canonical identity
modification. -/
@[simp]
theorem toModification_id (ψ : S ⟶ T) :
    toModification (𝟙 ψ) =
      CospanTransform.Hom.id (Hom.toCospanTransform ψ) := sorry

/-- Forgetting a vertical composite of bundled-cospan `2`-morphisms gives the vertical
composite of the underlying modifications. -/
@[simp]
theorem toModification_comp
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    toModification (Γ ≫ Δ) =
      CospanTransform.Hom.comp (toModification Γ)
        (toModification Δ) := sorry

/-- The left component of an identity bundled-cospan `2`-morphism is an identity cell. -/
@[simp]
theorem id_left (ψ : S ⟶ T) :
    left (𝟙 ψ) = 𝟙 (Hom.left ψ) := sorry

/-- The right component of an identity bundled-cospan `2`-morphism is an identity cell. -/
@[simp]
theorem id_right (ψ : S ⟶ T) :
    right (𝟙 ψ) = 𝟙 (Hom.right ψ) := sorry

/-- The common-target component of an identity bundled-cospan `2`-morphism is an identity
cell. -/
@[simp]
theorem id_base (ψ : S ⟶ T) :
    base (𝟙 ψ) = 𝟙 (Hom.base ψ) := sorry

/-- The left component of a vertical composite is the vertical composite of left
components. -/
@[simp]
theorem comp_left (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    left (Γ ≫ Δ) = left Γ ≫ left Δ := sorry

/-- The right component of a vertical composite is the vertical composite of right
components. -/
@[simp]
theorem comp_right (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    right (Γ ≫ Δ) = right Γ ≫ right Δ := sorry

/-- The common-target component of a vertical composite is the vertical composite of
common-target components. -/
@[simp]
theorem comp_base (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    base (Γ ≫ Δ) = base Γ ≫ base Δ := sorry

end Hom₂

/-- The cospan inclusion forgets a bundled-cospan `2`-morphism to its underlying
modification. -/
@[simp]
theorem inclusion_map₂
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (inclusion B).map₂ Γ = Hom₂.toModification Γ := sorry

/- Data and axiom audit (mathlib 4.32):

`#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for
`ofModification`, `modificationEquiv`, and `mk`. Source inspection shows that they reuse the
induced-bicategory wrapper and canonical `CospanTransform.Hom.mk`, with all three component
cells explicit. Thus `sorryAx` is confined to naturality, wrapper equality, and computation
theorems and cannot choose a cell. -/

end CategoryTheory.Bicategory.Cospan
