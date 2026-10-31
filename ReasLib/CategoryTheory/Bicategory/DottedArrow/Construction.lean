/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-
`Bicategory.PseudoPullbackCone y p` is the canonical owner of the solid boundary

```
                              sq.snd
                   sq.pt ─────────────────────────▶ X
                     │                         ↗    │
              sq.fst │              A.arrow  ╱      │ p
                     ▼                     ╱        ▼
                     T ───────────────────────────▶ Y
                                   y
```

The rising diagonal is the dotted arrow `A.arrow : T ⟶ X`. Its two triangular comparisons say
that going around either triangle agrees with the corresponding solid edge. For
`A : DottedArrow sq`, their compatibility with the outer square is the commutativity of

```
                                outer square: sq.iso
      sq.fst ≫ y ─────────────────────────────────────────────▶ sq.snd ≫ p
           │                                                           ▲
 left      │                                                           │ right
 triangle  ▼                                                           │ triangle
      sq.fst ≫ (A.arrow ≫ p) ─────────────────────────▶
                    (sq.fst ≫ A.arrow) ≫ p
                              reassociate
```

Here “left triangle” is `whiskerLeftIso sq.fst A.right`, “reassociate” is
`(α_ sq.fst A.arrow p).symm`, and “right triangle” is `whiskerRightIso A.left p`.

Mathlib's `LeftLift p y` owns `A.arrow` and the lower-right comparison, and its morphisms own
the `right_comm` equation. It does not store the upper-left comparison or its compatibility with
`sq.iso`. Using it as the root would therefore require another dependent subtype around an
already nested `StructuredArrow`. Likewise, an iso-comma/equifier presentation inside the hom
categories is a valid semantic model, but it would replace the four direct source fields by a
heavier dependent representation.

The explicit object and morphism structures below form the bundled category `DottedArrow sq`.
The data apply to an arbitrary bicategory by storing both comparisons as isomorphisms;
adding `[Bicategory.IsLocallyGroupoid B]` gives the locally groupoidal setting.
-/

namespace DottedArrow

/-- A dotted arrow for the `2`-commutative square `sq` is a morphism
`arrow : T ⟶ X`, invertible `2`-morphisms from `sq.fst ≫ arrow` to `sq.snd` and from `y` to
`arrow ≫ p`, and the stated compatibility with the chosen outer comparison `sq.iso`. -/
@[stacks 0H18 "dotted-arrow data and triangular coherence"]
structure Object
    {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
    (sq : Bicategory.PseudoPullbackCone y p) where
  /-- The dotted morphism from the lower-left object to the upper-right object. -/
  arrow : T ⟶ X
  /-- The comparison `2`-isomorphism for the upper-left triangle. -/
  left : sq.fst ≫ arrow ≅ sq.snd
  /-- The comparison `2`-isomorphism for the lower-right triangle. -/
  right : y ≅ arrow ≫ p
  /-- The two triangular comparisons compose to the chosen outer comparison. -/
  comm :
    whiskerLeftIso sq.fst right ≪≫
        (α_ sq.fst arrow p).symm ≪≫ whiskerRightIso left p =
      sq.iso

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : Bicategory.PseudoPullbackCone y p}

/-- Construct a dotted-arrow object from its morphism, triangular comparisons, and coherence. -/
def Object.ofComponents (arrow : T ⟶ X) (left : sq.fst ≫ arrow ≅ sq.snd)
    (right : y ≅ arrow ≫ p)
    (comm : whiskerLeftIso sq.fst right ≪≫
      (α_ sq.fst arrow p).symm ≪≫ whiskerRightIso left p = sq.iso) : Object sq :=
  ⟨arrow, left, right, comm⟩

/-- A morphism of dotted arrows is a `2`-morphism between their dotted
morphisms that is compatible with both triangular comparison `2`-isomorphisms. -/
@[stacks 0H18 "morphisms of dotted arrows and comparison compatibility"]
structure Hom (A A' : Object sq) where
  /-- The ambient `2`-morphism between the dotted morphisms. -/
  hom : A.arrow ⟶ A'.arrow
  /-- Compatibility with the upper-left comparison `2`-isomorphisms. -/
  left_comm : sq.fst ◁ hom ≫ A'.left.hom = A.left.hom
  /-- Compatibility with the lower-right comparison `2`-isomorphisms. -/
  right_comm : A.right.hom ≫ hom ▷ p = A'.right.hom

/-- Compatible dotted-arrow morphisms are determined by their ambient `2`-morphism. -/
@[ext]
theorem Hom.ext {A A' : Object sq} {η θ : Hom A A'} (h : η.hom = θ.hom) : η = θ := by
  cases η with
  | mk η η_left η_right =>
    cases θ with
    | mk θ θ_left θ_right =>
      cases h
      rfl

section Category

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Left-triangle compatibility for the identity morphism of a dotted arrow.

Proof strategy: use `Bicategory.whiskerLeft_id`, then cancel the resulting unitors with
the ambient category identity laws. -/
private theorem idHom_left_comm (A : Object sq) :
    sq.fst ◁ 𝟙 A.arrow ≫ A.left.hom = A.left.hom := by
  simp

/-- Right-triangle compatibility for the identity morphism of a dotted arrow.

Proof strategy: use `Bicategory.id_whiskerRight`, then cancel the resulting unitors with
the ambient category identity laws. -/
private theorem idHom_right_comm (A : Object sq) :
    A.right.hom ≫ 𝟙 A.arrow ▷ p = A.right.hom := by
  simp

end Implementation

/-- The identity compatible morphism of a dotted-arrow object. -/
def idHom (A : Object sq) : Hom A A where
  hom := 𝟙 A.arrow
  left_comm := Implementation.idHom_left_comm A
  right_comm := Implementation.idHom_right_comm A

namespace Implementation

/-- Left-triangle compatibility for composition of dotted-arrow morphisms.

Proof strategy: rewrite with `Bicategory.whiskerLeft_comp`, reassociate, and apply the
two input `left_comm` equations. -/
private theorem compHom_left_comm
    {A A' A'' : Object sq} (η : Hom A A') (θ : Hom A' A'') :
    sq.fst ◁ (η.hom ≫ θ.hom) ≫ A''.left.hom = A.left.hom := by
  rw [Bicategory.whiskerLeft_comp, Category.assoc, θ.left_comm, η.left_comm]

/-- Right-triangle compatibility for composition of dotted-arrow morphisms.

Proof strategy: rewrite with `Bicategory.comp_whiskerRight`, reassociate, and apply the
two input `right_comm` equations. -/
private theorem compHom_right_comm
    {A A' A'' : Object sq} (η : Hom A A') (θ : Hom A' A'') :
    A.right.hom ≫ (η.hom ≫ θ.hom) ▷ p = A''.right.hom := by
  rw [Bicategory.comp_whiskerRight, ← Category.assoc, η.right_comm, θ.right_comm]

end Implementation

/-- Composition of compatible morphisms of dotted-arrow objects. -/
def compHom
    {A A' A'' : Object sq} (η : Hom A A') (θ : Hom A' A'') : Hom A A'' where
  hom := η.hom ≫ θ.hom
  left_comm := Implementation.compHom_left_comm η θ
  right_comm := Implementation.compHom_right_comm η θ

namespace Implementation

/-- Left identity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.id_comp`. -/
private theorem idHom_comp {A A' : Object sq} (η : Hom A A') :
    compHom (idHom A) η = η := by
  apply Hom.ext
  exact Category.id_comp η.hom

/-- Right identity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.comp_id`. -/
private theorem comp_idHom {A A' : Object sq} (η : Hom A A') :
    compHom η (idHom A') = η := by
  apply Hom.ext
  exact Category.comp_id η.hom

/-- Associativity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.assoc`. -/
private theorem compHom_assoc {A₀ A₁ A₂ A₃ : Object sq}
    (η : Hom A₀ A₁) (θ : Hom A₁ A₂) (ι : Hom A₂ A₃) :
    compHom (compHom η θ) ι = compHom η (compHom θ ι) := by
  apply Hom.ext
  exact Category.assoc η.hom θ.hom ι.hom

end Implementation

/-- The category structure on dotted-arrow objects, with compatible ambient `2`-morphisms. -/
@[reducible]
def category : Category (Object sq) where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp := Implementation.idHom_comp
  comp_id := Implementation.comp_idHom
  assoc := Implementation.compHom_assoc

end

end Category

end DottedArrow

/-- The bundled category of dotted arrows compatible with a fixed `2`-commutative square. -/
def DottedArrow {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
    (sq : Bicategory.PseudoPullbackCone y p) : Cat.{w, max w v} :=
  ⟨DottedArrow.Object sq, DottedArrow.category⟩

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : Bicategory.PseudoPullbackCone y p}

/-- The underlying `2`-morphism of the identity dotted-arrow morphism is the identity. -/
@[simp]
theorem id_hom (A : DottedArrow sq) :
    (𝟙 A : A ⟶ A).hom = 𝟙 A.arrow := rfl

/-- The underlying `2`-morphism of a composite dotted-arrow morphism is the composite of the
underlying `2`-morphisms. -/
@[simp]
theorem comp_hom {A A' A'' : DottedArrow sq} (η : A ⟶ A') (θ : A' ⟶ A'') :
    (η ≫ θ).hom = η.hom ≫ θ.hom := rfl

end DottedArrow

end CategoryTheory
