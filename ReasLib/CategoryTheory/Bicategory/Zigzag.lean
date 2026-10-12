/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.IsConnected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zigzags under bicategorical composition

Whiskering and horizontal composition preserve zigzag-connectedness in hom-categories.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory.Zigzag

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Left whiskering by a fixed `1`-morphism preserves zigzag-connectedness. The bundled action
is mathlib's `Bicategory.precomp`; this theorem records its action on connectedness. -/
theorem whiskerLeft
    {X Y Z : B} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (hg : CategoryTheory.Zigzag g g') :
    CategoryTheory.Zigzag (f ≫ g) (f ≫ g') := sorry

/-- Right whiskering by a fixed `1`-morphism preserves zigzag-connectedness. The bundled action
is mathlib's `Bicategory.postcomp`; this theorem records its action on connectedness. -/
theorem whiskerRight
    {X Y Z : B} {f f' : X ⟶ Y}
    (hf : CategoryTheory.Zigzag f f') (g : Y ⟶ Z) :
    CategoryTheory.Zigzag (f ≫ g) (f' ≫ g) := sorry

/-- Horizontal composition in a bicategory preserves zigzag-connectedness in both variables. -/
@[stacks 04SC "horizontal composition preserves zigzags"]
theorem comp
    {X Y Z : B} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : CategoryTheory.Zigzag f f') (hg : CategoryTheory.Zigzag g g') :
    CategoryTheory.Zigzag (f ≫ g) (f' ≫ g') := sorry

end CategoryTheory.Bicategory.Zigzag
