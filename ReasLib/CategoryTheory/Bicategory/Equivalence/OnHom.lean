/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Composition

/-!
# Adjoint-equivalence structures on fixed bicategorical morphisms

This module owns chosen adjoint-equivalence data whose forward `1`-morphism
is fixed in advance. It is the equivalence analogue of
`Bicategory.RightAdjoint`: the carrier morphism is not duplicated, while the
chosen inverse, unit, counit, and triangle coherence remain explicit data.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory.Equivalence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B}

/-- Chosen adjoint-equivalence data on a fixed `1`-morphism.

Unlike `Bicategory.Equivalence x y`, this owner does not store a second copy
of the forward morphism. This avoids equality transports when equivalence data
must be attached to a morphism already present in another structure. -/
@[stacks 0040 "adjoint-equivalence data on a fixed morphism"]
structure OnHom (hom : x ⟶ y) where
  /-- The chosen inverse of the fixed forward morphism. -/
  inv : y ⟶ x
  /-- The unit isomorphism of the chosen adjoint equivalence. -/
  unit : 𝟙 x ≅ hom ≫ inv
  /-- The counit isomorphism of the chosen adjoint equivalence. -/
  counit : inv ≫ hom ≅ 𝟙 y
  /-- The unit and counit satisfy the left triangle identity. -/
  left_triangle :
    Bicategory.leftZigzagIso unit counit =
      λ_ hom ≪≫ (ρ_ hom).symm

namespace OnHom

variable {f : x ⟶ y} {g : y ⟶ z}

/-- Assemble fixed-morphism adjoint-equivalence data into a bicategorical
equivalence. -/
@[stacks 0040 "equivalence carried by fixed-morphism data"]
def toEquivalence (h : OnHom f) : x ≌ y where
  hom := f
  inv := h.inv
  unit := h.unit
  counit := h.counit
  left_triangle := h.left_triangle

/-- The forward morphism of the assembled equivalence is the fixed morphism. -/
@[simp]
theorem toEquivalence.hom (h : OnHom f) :
    h.toEquivalence.hom = f := sorry

/-- The inverse morphism of the assembled equivalence is the chosen inverse. -/
@[simp]
theorem toEquivalence.inv (h : OnHom f) :
    h.toEquivalence.inv = h.inv := sorry

/-- The unit of the assembled equivalence is the chosen unit. -/
@[simp]
theorem toEquivalence.unit (h : OnHom f) :
    h.toEquivalence.unit = h.unit := sorry

/-- The counit of the assembled equivalence is the chosen counit. -/
@[simp]
theorem toEquivalence.counit (h : OnHom f) :
    h.toEquivalence.counit = h.counit := sorry

/-- Forget invertibility while retaining the chosen right adjoint of the fixed
forward morphism. -/
@[stacks 0040 "right adjoint carried by fixed-morphism equivalence data"]
def toRightAdjoint (h : OnHom f) : Bicategory.RightAdjoint f :=
  ⟨h.inv, h.toEquivalence.toAdjunction⟩

/-- The right adjoint retained by `toRightAdjoint` is the chosen inverse. -/
@[simp]
theorem toRightAdjoint.right (h : OnHom f) :
    h.toRightAdjoint.right = h.inv := sorry

/-- The adjunction retained by `toRightAdjoint` underlies the assembled
equivalence. -/
@[simp]
theorem toRightAdjoint.adj (h : OnHom f) :
    h.toRightAdjoint.adj = h.toEquivalence.toAdjunction := sorry

/-- The unit obtained by replacing the fixed forward morphism along an
invertible `2`-cell. -/
@[stacks 0040 "unit after changing a fixed equivalence morphism"]
def changeHom.unitIso {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    𝟙 x ≅ f' ≫ h.inv :=
  h.unit ≪≫ Bicategory.whiskerRightIso i h.inv

/-- The counit obtained by replacing the fixed forward morphism along an
invertible `2`-cell. -/
@[stacks 0040 "counit after changing a fixed equivalence morphism"]
def changeHom.counitIso {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    h.inv ≫ f' ≅ 𝟙 y :=
  (Bicategory.whiskerLeftIso h.inv i).symm ≪≫ h.counit

/-- Changing the fixed forward morphism preserves the left triangle
identity. -/
private theorem Implementation.changeHom.left_triangle
    {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    Bicategory.leftZigzagIso
        (changeHom.unitIso h i) (changeHom.counitIso h i) =
      λ_ f' ≪≫ (ρ_ f').symm := sorry

/-- Transport adjoint-equivalence data along an invertible `2`-cell between
forward morphisms.

This is the bicategorically natural alignment operation: callers provide the
comparison cell itself rather than an equality between morphisms. -/
@[stacks 0040 "change the forward morphism of fixed equivalence data"]
def changeHom {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') : OnHom f' where
  inv := h.inv
  unit := changeHom.unitIso h i
  counit := changeHom.counitIso h i
  left_triangle := Implementation.changeHom.left_triangle h i

/-- Changing the forward morphism retains the chosen inverse. -/
@[simp]
theorem changeHom.inv {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    (h.changeHom i).inv = h.inv := sorry

/-- Changing the forward morphism uses the explicitly conjugated unit. -/
@[simp]
theorem changeHom.unit {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    (h.changeHom i).unit = changeHom.unitIso h i := sorry

/-- Changing the forward morphism uses the explicitly conjugated counit. -/
@[simp]
theorem changeHom.counit {f' : x ⟶ y} (h : OnHom f) (i : f ≅ f') :
    (h.changeHom i).counit = changeHom.counitIso h i := sorry

/-- Restrict a bicategorical equivalence to adjoint-equivalence data on its
forward morphism. -/
@[stacks 0040 "fixed-morphism data of a bicategorical equivalence"]
def ofEquivalence (e : x ≌ y) : OnHom e.hom where
  inv := e.inv
  unit := e.unit
  counit := e.counit
  left_triangle := e.left_triangle

/-- Restricting an equivalence and then assembling it recovers the original
equivalence. -/
@[simp]
theorem ofEquivalence.toEquivalence (e : x ≌ y) :
    (ofEquivalence e).toEquivalence = e := sorry

/-- Assembling fixed-morphism data and then restricting it recovers the
original data. -/
@[simp]
theorem toEquivalence.ofEquivalence (h : OnHom f) :
    ofEquivalence h.toEquivalence = h := sorry

/-- The identity morphism carries its canonical identity equivalence data. -/
@[stacks 0040 "fixed-morphism identity equivalence data"]
def id (x : B) : OnHom (𝟙 x) :=
  ofEquivalence (Bicategory.Equivalence.id x)

/-- Reverse fixed-morphism equivalence data, using the chosen inverse as the
new forward morphism. -/
@[stacks 0040 "reverse fixed-morphism equivalence data"]
def symm (h : OnHom f) : OnHom h.inv :=
  ofEquivalence h.toEquivalence.symm

/-- Compose fixed-morphism equivalence data. -/
@[stacks 0040 "compose fixed-morphism equivalence data"]
def trans (hf : OnHom f) (hg : OnHom g) : OnHom (f ≫ g) :=
  ofEquivalence (hf.toEquivalence.trans hg.toEquivalence)

/-- The inverse chosen for composite fixed-morphism data is the reverse
composite of the chosen inverses. -/
@[simp]
theorem trans.inv (hf : OnHom f) (hg : OnHom g) :
    (trans hf hg).inv = hg.inv ≫ hf.inv := sorry

/-- The unit chosen for composite fixed-morphism data is the canonical
composite unit. -/
@[simp]
theorem trans.unit (hf : OnHom f) (hg : OnHom g) :
    (trans hf hg).unit =
      Bicategory.Equivalence.trans.unitIso
        hf.toEquivalence hg.toEquivalence := sorry

/-- The counit chosen for composite fixed-morphism data is the canonical
composite counit. -/
@[simp]
theorem trans.counit (hf : OnHom f) (hg : OnHom g) :
    (trans hf hg).counit =
      Bicategory.Equivalence.trans.counitIso
        hf.toEquivalence hg.toEquivalence := sorry

/- Data audit (mathlib 4.32): `OnHom` owns all non-`Prop` inverse, unit, and
counit data explicitly. `toEquivalence`, `toRightAdjoint`, `ofEquivalence`,
`changeHom`, `id`, `symm`, and `trans` only repackage canonical data; deferred
content is confined to triangle fields and projection/round-trip
propositions. -/

end OnHom

end Bicategory.Equivalence

end CategoryTheory
