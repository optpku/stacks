/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Readable bicategorical pseudopullback cones

This file defines only the elementary, source-facing presentation of a pseudopullback cone.
The shape-independent semantic owner and universal property belong to
`CategoryTheory.Bicategory.PseudoCone`; their comparison with this four-field presentation is
provided by a separate bilimit module.

Keeping the raw cone data independent of walking-cospan diagrams, bilimits, transport, and
equivalence machinery lets downstream statements import the conventional square notation
without acquiring the full pseudopullback infrastructure.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} (f : x ⟶ z) (g : y ⟶ z)

namespace PseudoPullbackCone

/-- A readable cospan-shaped presentation of a pseudocone over `x ⟶ z ← y`:

```text
       pt ───────────── fst ─────────────▶ x
       │                                     │
   snd │               ⇓ iso.hom             │ f
       │                                     │
       ▼                                     ▼
       y ─────────────── g ─────────────────▶ z
```

The cell `iso.hom` is oriented from `fst ≫ f` to `snd ≫ g`. This structure contains only the
concrete square data; its universal property and relationship with the neutral
`PseudoCone (cospan f g)` owner are deliberately layered above this file. -/
@[stacks 0H19 "2-commutative square in a dotted-arrow diagram", ext]
structure Square where
  /-- The apex object of the square. -/
  pt : B
  /-- The projection to the left object. -/
  fst : pt ⟶ x
  /-- The projection to the right object. -/
  snd : pt ⟶ y
  /-- The invertible `2`-morphism witnessing `2`-commutativity. -/
  iso : fst ≫ f ≅ snd ≫ g

end PseudoPullbackCone

/-- The canonical categorical pseudopullback carrier associated to an explicit square. -/
def PseudoPullbackCone {B : Type u} [Bicategory.{w, v} B] {x y z : B}
    (f : x ⟶ z) (g : y ⟶ z) := PseudoPullbackCone.Square f g

namespace PseudoPullbackCone

/-- Construct a pseudopullback square from its apex, projections, and comparison isomorphism. -/
def Square.ofComponents (pt : B) (fst : pt ⟶ x) (snd : pt ⟶ y)
    (iso : fst ≫ f ≅ snd ≫ g) : PseudoPullbackCone.Square f g :=
  ⟨pt, fst, snd, iso⟩

/-- Construct the canonical pseudopullback cone from its four displayed components. -/
def mk (pt : B) (fst : pt ⟶ x) (snd : pt ⟶ y) (iso : fst ≫ f ≅ snd ≫ g) :
    PseudoPullbackCone f g :=
  Square.ofComponents f g pt fst snd iso

/-- The apex of a pseudopullback cone. -/
def pt (S : PseudoPullbackCone f g) : B := Square.pt S

/-- The left projection of a pseudopullback cone. -/
def fst (S : PseudoPullbackCone f g) : S.pt ⟶ x := Square.fst S

/-- The right projection of a pseudopullback cone. -/
def snd (S : PseudoPullbackCone f g) : S.pt ⟶ y := Square.snd S

/-- The comparison isomorphism of a pseudopullback cone. -/
def iso (S : PseudoPullbackCone f g) : S.fst ≫ f ≅ S.snd ≫ g := Square.iso S

/-- Equality of pseudopullback cones is determined by their four displayed components. -/
@[ext (iff := false)]
theorem ext {S T : PseudoPullbackCone f g} (hpt : S.pt = T.pt) (hfst : S.fst = hpt ▸ T.fst)
    (hsnd : S.snd = hpt ▸ T.snd) (hiso : HEq S.iso T.iso) : S = T := by
  cases S
  cases T
  cases hpt
  cases hfst
  cases hsnd
  cases hiso
  rfl

end PseudoPullbackCone

/- The structure stores its apex, both projections, and comparison isomorphism explicitly,
with no choice, quotient representative, or proof-only surrogate for these data. -/

end CategoryTheory.Bicategory
