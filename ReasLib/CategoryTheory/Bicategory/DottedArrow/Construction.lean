module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
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

The direct structures below are consequently the solution owner and its morphisms. There is no
separate `Solution`, `DottedArrowCategory`, or representability wrapper: `DottedArrow sq`
itself becomes the solution category in Lemma 4.44.2, while universal or representability
properties should be stated on that category. No notation is needed because the owner and its
projections are already short. The data generalize from a locally groupoidal bicategory to an
arbitrary bicategory by storing both comparisons as isomorphisms; adding
`[Bicategory.IsLocallyGroupoid B]` recovers the source setting.
-/

/-- A dotted arrow for the `2`-commutative square `sq` is a morphism
`arrow : T ⟶ X`, invertible `2`-morphisms from `sq.fst ≫ arrow` to `sq.snd` and from `y` to
`arrow ≫ p`, and the stated compatibility with the chosen outer comparison `sq.iso`. -/
@[stacks 0H18 "dotted-arrow data and triangular coherence"]
structure DottedArrow
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

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : Bicategory.PseudoPullbackCone y p}

/-- A morphism of dotted arrows is a `2`-morphism between their dotted
morphisms that is compatible with both triangular comparison `2`-isomorphisms. -/
@[stacks 0H18 "morphisms of dotted arrows and comparison compatibility"]
structure Hom (A A' : DottedArrow sq) where
  /-- The ambient `2`-morphism between the dotted morphisms. -/
  hom : A.arrow ⟶ A'.arrow
  /-- Compatibility with the upper-left comparison `2`-isomorphisms. -/
  left_comm : sq.fst ◁ hom ≫ A'.left.hom = A.left.hom
  /-- Compatibility with the lower-right comparison `2`-isomorphisms. -/
  right_comm : A.right.hom ≫ hom ▷ p = A'.right.hom

section Category

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Left-triangle compatibility for the identity morphism of a dotted arrow.

Proof strategy: use `Bicategory.whiskerLeft_id`, then cancel the resulting unitors with
the ambient category identity laws. -/
private theorem idHom_left_comm (A : DottedArrow sq) :
    sq.fst ◁ 𝟙 A.arrow ≫ A.left.hom = A.left.hom := sorry

/-- Right-triangle compatibility for the identity morphism of a dotted arrow.

Proof strategy: use `Bicategory.id_whiskerRight`, then cancel the resulting unitors with
the ambient category identity laws. -/
private theorem idHom_right_comm (A : DottedArrow sq) :
    A.right.hom ≫ 𝟙 A.arrow ▷ p = A.right.hom := sorry

/-- The identity morphism of a dotted arrow. -/
private def idHom (A : DottedArrow sq) : Hom A A where
  hom := 𝟙 A.arrow
  left_comm := idHom_left_comm A
  right_comm := idHom_right_comm A

/-- Left-triangle compatibility for composition of dotted-arrow morphisms.

Proof strategy: rewrite with `Bicategory.whiskerLeft_comp`, reassociate, and apply the
two input `left_comm` equations. -/
private theorem compHom_left_comm
    {A A' A'' : DottedArrow sq} (η : Hom A A') (θ : Hom A' A'') :
    sq.fst ◁ (η.hom ≫ θ.hom) ≫ A''.left.hom = A.left.hom := sorry

/-- Right-triangle compatibility for composition of dotted-arrow morphisms.

Proof strategy: rewrite with `Bicategory.comp_whiskerRight`, reassociate, and apply the
two input `right_comm` equations. -/
private theorem compHom_right_comm
    {A A' A'' : DottedArrow sq} (η : Hom A A') (θ : Hom A' A'') :
    A.right.hom ≫ (η.hom ≫ θ.hom) ▷ p = A''.right.hom := sorry

/-- Composition of dotted-arrow morphisms. -/
private def compHom
    {A A' A'' : DottedArrow sq} (η : Hom A A') (θ : Hom A' A'') : Hom A A'' where
  hom := η.hom ≫ θ.hom
  left_comm := compHom_left_comm η θ
  right_comm := compHom_right_comm η θ

/-- Left identity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.id_comp`. -/
private theorem idHom_comp {A A' : DottedArrow sq} (η : Hom A A') :
    compHom (idHom A) η = η := sorry

/-- Right identity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.comp_id`. -/
private theorem comp_idHom {A A' : DottedArrow sq} (η : Hom A A') :
    compHom η (idHom A') = η := sorry

/-- Associativity law for dotted-arrow morphisms.

Proof strategy: apply `Hom.ext`; the ambient component is `Category.assoc`. -/
private theorem compHom_assoc {A₀ A₁ A₂ A₃ : DottedArrow sq}
    (η : Hom A₀ A₁) (θ : Hom A₁ A₂) (ι : Hom A₂ A₃) :
    compHom (compHom η θ) ι = compHom η (compHom θ ι) := sorry

end Implementation

/- Mathlib's `LeftLift` owns one triangle but not the second comparison or the outer coherence;
the dependency's source-facing `DottedArrow` is therefore the exact owner. Its explicit `Hom`
structure supplies the canonical morphisms, so only the category operations and their
law proofs are added here. This keeps the source category available without a parallel wrapper. -/

/-- Dotted arrows for a fixed `2`-commutative square form a category. -/
instance category : Category (DottedArrow sq) where
  Hom := Hom
  id := Implementation.idHom
  comp := Implementation.compHom
  id_comp := Implementation.idHom_comp
  comp_id := Implementation.comp_idHom
  assoc := Implementation.compHom_assoc

end

/-- The underlying `2`-morphism of the identity dotted-arrow morphism is the identity.

Proof strategy: unfold the private implementation selected by the category instance. -/
@[simp]
theorem id_hom (A : DottedArrow sq) :
    (𝟙 A : A ⟶ A).hom = 𝟙 A.arrow := sorry

/-- The underlying `2`-morphism of a composite dotted-arrow morphism is the composite of the
underlying `2`-morphisms.

Proof strategy: unfold the private implementation selected by the category instance. -/
@[simp]
theorem comp_hom {A A' A'' : DottedArrow sq} (η : A ⟶ A') (θ : A' ⟶ A'') :
    (η ≫ θ).hom = η.hom ≫ θ.hom := sorry

end Category

end DottedArrow

end CategoryTheory
