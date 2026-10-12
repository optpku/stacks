/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Basic

/-!
# Postcomposition of morphisms of colax costructured arrows

A fixed target `1`-morphism postcomposes the structural maps of colax
costructured arrows and transports their `1`- and `2`-morphisms. Source maps and
source `2`-cells are retained; only the normalized comparison cell is pasted
with an associator and right whiskered.

This file contains the data-level action and its projection formulas. Identity,
composition, and pseudofunctor coherence are kept in downstream modules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

/-- The normalized comparison cell of a costructured-arrow morphism after
postcomposing its structural maps.

The inverse associator exposes the original comparison as a left factor; right
whiskering then postcomposes that comparison by `f`. -/
def fac
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ((obj f T).comparison S.left).obj
        (ColaxCostructuredArrow.map (K := K) (X := X) u) ⟶
      (obj f S).hom :=
  (α_ (K.map (ColaxCostructuredArrow.map (K := K) (X := X) u))
      T.hom f).inv ≫
    ColaxCostructuredArrow.fac (K := K) (X := X) u ▷ f

/-- The postcomposed normalized comparison is the inverse associator followed
by right whiskering of the original comparison. -/
@[simp]
theorem fac.eq
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    fac f u =
      (α_ (K.map
        (ColaxCostructuredArrow.map (K := K) (X := X) u))
        T.hom f).inv ≫
        ColaxCostructuredArrow.fac (K := K) (X := X) u ▷ f := sorry

/-- Postcompose a morphism of colax costructured arrows by a target
`1`-morphism. Its source map is unchanged and its normalized comparison is
`postcompose.fac`. -/
def map
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    obj f S ⟶ obj f T :=
  ColaxCostructuredArrow.homMk (K := K) (X := Y)
    (ColaxCostructuredArrow.map (K := K) (X := X) u :
      S.left ⟶ T.left)
    (fac f u)

/-- Postcomposition of a costructured-arrow morphism leaves its source map
unchanged. -/
@[simp]
theorem map.underlying
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
        (map f u) =
      ColaxCostructuredArrow.map (K := K) (X := X) u := sorry

/-- The normalized comparison of a postcomposed costructured-arrow morphism is
`postcompose.fac`. -/
@[simp]
theorem map.fac
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.fac (K := K) (X := Y)
        (map f u) =
      fac f u := sorry

namespace Implementation

/-- Compatibility of an unchanged source cell with postcomposed normalized
comparisons. -/
private theorem map₂_comm
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (η : u ⟶ v) :
    ((obj f T).comparison S.left).map
          (ColaxCostructuredArrow.map₂ (K := K) (X := X) η) ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (map f v) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (map f u) := sorry

end Implementation

/-- Postcompose a `2`-morphism of colax costructured arrows by a target
`1`-morphism. Its source `2`-cell is unchanged. -/
def map₂
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (η : u ⟶ v) :
    map f u ⟶ map f v :=
  ColaxCostructuredArrow.hom₂Mk (K := K) (X := Y)
    (ColaxCostructuredArrow.map₂ (K := K) (X := X) η)
    (Implementation.map₂_comm f η)

/-- Postcomposition of a costructured-arrow `2`-morphism leaves its source cell
unchanged. -/
@[simp]
theorem map₂.underlying
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (η : u ⟶ v) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (map₂ f η) =
      ColaxCostructuredArrow.map₂ (K := K) (X := X) η := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.fac` is the explicit associator-and-whiskering pasting.
`postcompose.map` retains the original source map, and `postcompose.map₂` retains
the original source cell. Their remaining bundled fields are normalized
comparison or compatibility proofs; no morphism or cell is selected by an
existence witness. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
