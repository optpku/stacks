/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Hom

/-!
# Composition comparison for postcomposition of costructured arrows

For a fixed target `1`-morphism, postcomposition carries a composite of
costructured-arrow morphisms to the composite of their images up to an
invertible `2`-morphism. This file constructs that comparison through
`ColaxCostructuredArrow.iso₂Mk`.

The source-map isomorphism is the identity on the unchanged composite source
map. Compatibility is an implementation detail; the public API exposes the
comparison and its source-cell computations.
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

namespace Implementation

/-- The source-map isomorphism underlying the composition comparison for
postcomposition. -/
private def mapComp.sourceIso
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
          (map f (u ≫ v)) ≅
      ColaxCostructuredArrow.map (K := K) (X := Y)
        (map f u ≫ map f v) :=
  Iso.refl
    (ColaxCostructuredArrow.map (K := K) (X := X) u ≫
      ColaxCostructuredArrow.map (K := K) (X := X) v)

/-- Compatibility of the source-map identity isomorphism with the normalized
comparisons of the mapped composite and the composite of mapped morphisms. -/
private theorem mapComp.comm
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ((obj f T).comparison R.left).map
          (mapComp.sourceIso f u v).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (map f u ≫ map f v) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (map f (u ≫ v)) := sorry

end Implementation

/-- The composition comparison for postcomposition of colax costructured
arrows.

Its forward and inverse source cells are both the identity `2`-morphism of the
unchanged composite source map. -/
def mapComp
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    map f (u ≫ v) ≅
      map f u ≫ map f v :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.mapComp.sourceIso f u v)
    (Implementation.mapComp.comm f u v)

/-- The source cell of the forward composition comparison is the identity. -/
@[simp]
theorem mapComp.hom.map₂
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (mapComp f u v).hom =
      𝟙 (ColaxCostructuredArrow.map (K := K) (X := X) u ≫
        ColaxCostructuredArrow.map (K := K) (X := X) v) := sorry

/-- The source cell of the inverse composition comparison is the identity. -/
@[simp]
theorem mapComp.inv.map₂
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (mapComp f u v).inv =
      𝟙 (ColaxCostructuredArrow.map (K := K) (X := X) u ≫
        ColaxCostructuredArrow.map (K := K) (X := X) v) := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.mapComp` reuses `ColaxCostructuredArrow.iso₂Mk` with the explicit
identity isomorphism of the unchanged composite source map. The only new
deferred statement is comparison compatibility; no composite map or `2`-cell
is selected through a proof placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
