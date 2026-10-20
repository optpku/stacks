/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Component

/-!
# Naturality of target-cell postcomposition

For a target `2`-morphism `η : f ⟶ g`, the contravariant components
`postcompose.cellComponent η S` are strongly natural in the colax
costructured arrow `S`.

At a morphism `u : S ⟶ T`, naturality compares

`postcompose.map g u ≫ postcompose.cellComponent η T`

with

`postcompose.cellComponent η S ≫ postcompose.map f u`.

Their source maps differ only by unitors. The standard source-map isomorphism
`ρ_ _ ≪≫ (λ_ _).symm` is lifted through
`ColaxCostructuredArrow.iso₂Mk`. Coherence for assembling these isomorphisms
into a strong transformation is kept in a separate module.
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

/-- The standard unitor isomorphism between the source maps in target-cell
naturality. -/
private def cellNaturality.sourceIso
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
          (map g u ≫
            cellComponent η T) ≅
      ColaxCostructuredArrow.map (K := K) (X := Y)
        (cellComponent η S ≫
          map f u) :=
  ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
    (λ_ (ColaxCostructuredArrow.map (K := K) (X := X) u)).symm

/-- Compatibility of the source-map unitor isomorphism with the two normalized
costructured-arrow comparisons in target-cell naturality. -/
private theorem cellNaturality.comm
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ((obj f T).comparison S.left).map
          (cellNaturality.sourceIso η u).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (cellComponent η S ≫
            map f u) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (map g u ≫
          cellComponent η T) := sorry

end Implementation

/-- The strong naturality isomorphism of the contravariant component induced
by a target `2`-morphism.

Its source-map isomorphism is the standard comparison from
`map u ≫ 𝟙 _` to `𝟙 _ ≫ map u`. -/
def cellNaturality
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    map g u ≫ cellComponent η T ≅
      cellComponent η S ≫ map f u :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.cellNaturality.sourceIso η u)
    (Implementation.cellNaturality.comm η u)

/-- The forward source cell of target-cell naturality is the standard
right-to-left unitor comparison. -/
@[simp]
theorem cellNaturality.hom.map₂
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (cellNaturality η u).hom =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).hom := sorry

/-- The inverse source cell of target-cell naturality is the inverse standard
unitor comparison. -/
@[simp]
theorem cellNaturality.inv.map₂
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (cellNaturality η u).inv =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.cellNaturality` reuses `ColaxCostructuredArrow.iso₂Mk`. Its
source-map isomorphism is the explicit composite of the ambient right unitor
with the inverse left unitor. The only new deferred content is normalized
comparison compatibility; no source cell or inverse is selected through a
proof placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
