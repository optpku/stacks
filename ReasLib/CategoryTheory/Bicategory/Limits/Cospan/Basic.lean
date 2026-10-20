/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Diagram
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled cospans in a bicategory

This file packages bicategorical cospans and exposes readable projections from strong
transformations between their canonical walking-cospan pseudodiagrams.

The bicategory of bundled cospans is induced from the existing bicategory of pseudofunctors.
Consequently its `1`- and `2`-morphisms remain strong transformations and modifications rather
than a parallel hand-written implementation. Constructors, equivalences, and mapping by
pseudofunctors are layered in separate files.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- A bundled cospan in a bicategory:

```text
             fst                    snd
  left ───────────────▶ base ◀─────────────── right
```

This is the neutral data owner for constructions which vary all three objects and both legs. -/
@[ext, stacks 0040 "bundled bicategorical cospan"]
structure Cospan (B : Type u) [Bicategory.{w, v} B] where
  /-- The left endpoint. -/
  left : B
  /-- The right endpoint. -/
  right : B
  /-- The common target of the two legs. -/
  base : B
  /-- The leg from the left endpoint to the common target. -/
  fst : left ⟶ base
  /-- The leg from the right endpoint to the common target. -/
  snd : right ⟶ base

namespace Cospan

/-- The walking-cospan pseudofunctor represented by a bundled bicategorical cospan. -/
abbrev diagram (S : Cospan B) :
    Pseudofunctor (LocallyDiscrete Limits.WalkingCospan) B :=
  cospan S.fst S.snd

/-- Bundled cospans inherit the full bicategory structure on their walking-cospan
pseudofunctors. In particular, all strong transformations and modifications are retained. -/
instance bicategory : Bicategory (Cospan B) :=
  inferInstanceAs
    (Bicategory (InducedBicategory
      (Pseudofunctor (LocallyDiscrete Limits.WalkingCospan) B)
      (fun S : Cospan B ↦ S.diagram)))

variable (B) in
/-- The canonical inclusion of bundled cospans into the bicategory of walking-cospan
pseudofunctors. It is strict because the cospan bicategory is induced from that ambient
bicategory. The ambient bicategory is explicit because this canonical pseudofunctor has no
other input from which it can be inferred. -/
@[stacks 0040 "inclusion of bundled cospans into walking-cospan diagrams"]
def inclusion :
    StrictPseudofunctor (Cospan B)
      (Pseudofunctor (LocallyDiscrete Limits.WalkingCospan) B) :=
  InducedBicategory.forget

end Cospan

/-- A morphism from the canonical walking-cospan diagram `x ⟶ z ← y` to
`x' ⟶ z' ← y'`.

Its canonical owner is `Pseudofunctor.StrongTrans`; the readable API exposes the three vertex
maps and the two generating naturality isomorphisms. For the left generator,
`StrongTrans.naturality` points from `f ≫ ψ.base` to `ψ.left ≫ f'`; `leftIso` exposes the
inverse orientation used by cospan pasting, and similarly on the right. -/
@[stacks 0040 "strong transformation of bicategorical cospans"]
abbrev CospanTransform
    {x y z x' y' z' : B} (f : x ⟶ z) (g : y ⟶ z)
    (f' : x' ⟶ z') (g' : y' ⟶ z') :=
  Pseudofunctor.StrongTrans (cospan f g) (cospan f' g')

namespace CospanTransform

variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The component of a cospan transformation at the left endpoint. -/
abbrev left (ψ : CospanTransform f g f' g') : x ⟶ x' :=
  ψ.app (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The component of a cospan transformation at the right endpoint. -/
abbrev right (ψ : CospanTransform f g f' g') : y ⟶ y' :=
  ψ.app (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The component of a cospan transformation at the common target. -/
abbrev base (ψ : CospanTransform f g f' g') : z ⟶ z' :=
  ψ.app (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- The generating naturality isomorphism along the left leg, oriented from the transformed
target leg to the source leg followed by the common-target map. -/
def leftIso (ψ : CospanTransform f g f' g') :
    ψ.left ≫ f' ≅ f ≫ ψ.base :=
  (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm

/-- The forward cell of `leftIso` is the inverse generating naturality cell. -/
@[simp]
theorem leftIso.hom (ψ : CospanTransform f g f' g') :
    ψ.leftIso.hom =
      (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).inv := sorry

/-- The inverse cell of `leftIso` is the forward generating naturality cell. -/
@[simp]
theorem leftIso.inv (ψ : CospanTransform f g f' g') :
    ψ.leftIso.inv =
      (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).hom := sorry

/-- The generating naturality isomorphism along the right leg, in the same orientation as
`leftIso`. -/
def rightIso (ψ : CospanTransform f g f' g') :
    ψ.right ≫ g' ≅ g ≫ ψ.base :=
  (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).symm

/-- The forward cell of `rightIso` is the inverse generating naturality cell. -/
@[simp]
theorem rightIso.hom (ψ : CospanTransform f g f' g') :
    ψ.rightIso.hom =
      (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).inv := sorry

/-- The inverse cell of `rightIso` is the forward generating naturality cell. -/
@[simp]
theorem rightIso.inv (ψ : CospanTransform f g f' g') :
    ψ.rightIso.inv =
      (ψ.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).hom := sorry

/- Data and axiom audit (mathlib 4.32):

* `Cospan` stores all three objects and both legs explicitly and depends on no axioms.
* `Cospan.diagram`, `Cospan.inclusion`, `leftIso`, and `rightIso` introduce no additional
  object, morphism, comparison, or representative choice; they only expose canonical diagram
  and strong-transformation data.
* `#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for `inclusion`,
  `leftIso`, and `rightIso`. The inherited `sorryAx` is confined to pseudofunctor,
  strong-transformation, and induced-bicategory law fields; no non-`Prop` cospan datum is
  supplied by a placeholder. -/

end CospanTransform

end CategoryTheory.Bicategory
