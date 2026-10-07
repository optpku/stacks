module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic

/-!
# Isomorphisms between morphisms of colax costructured arrows

This file complements the normalized `ColaxCostructuredArrow.hom₂Mk` API with
an isomorphism constructor. An isomorphism between the source maps of two
costructured-arrow morphisms lifts whenever its forward cell is compatible with
their normalized comparison cells.

Only forward compatibility is requested publicly. Compatibility of the inverse
cell and the two inverse laws are derived as proof fields.
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
variable {K : Pseudofunctor A C} {X : C}

/-- Compatibility of the inverse source cell follows from compatibility of an
invertible forward source cell. -/
theorem iso₂Mk_inv_comm
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    (T.comparison S.left).map e.inv ≫
        ColaxCostructuredArrow.fac f =
      ColaxCostructuredArrow.fac g := sorry

namespace Implementation

/-- The lifted forward and inverse cells cancel on the source
costructured-arrow morphism. -/
private theorem iso₂Mk_hom_inv_id
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    ColaxCostructuredArrow.hom₂Mk e.hom comm ≫
        ColaxCostructuredArrow.hom₂Mk e.inv
          (iso₂Mk_inv_comm e comm) =
      𝟙 f := sorry

/-- The lifted inverse and forward cells cancel on the target
costructured-arrow morphism. -/
private theorem iso₂Mk_inv_hom_id
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    ColaxCostructuredArrow.hom₂Mk e.inv
          (iso₂Mk_inv_comm e comm) ≫
        ColaxCostructuredArrow.hom₂Mk e.hom comm =
      𝟙 g := sorry

end Implementation

/-- Construct an isomorphism between costructured-arrow `1`-morphisms from an
isomorphism between their source maps and forward compatibility with the
normalized comparison cells.

This is the normalized costructured-arrow analogue of
`ColaxComma.isoMk`; terminal-endpoint data are handled by
`ColaxCostructuredArrow.hom₂Mk`. -/
def iso₂Mk
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    f ≅ g where
  hom := ColaxCostructuredArrow.hom₂Mk e.hom comm
  inv := ColaxCostructuredArrow.hom₂Mk e.inv
    (iso₂Mk_inv_comm e comm)
  hom_inv_id := Implementation.iso₂Mk_hom_inv_id e comm
  inv_hom_id := Implementation.iso₂Mk_inv_hom_id e comm

/-- The source cell of the forward morphism constructed by `iso₂Mk` is the
forward cell of the supplied source-map isomorphism. -/
@[simp]
theorem iso₂Mk_hom_map₂
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    ColaxCostructuredArrow.map₂ (iso₂Mk e comm).hom =
      e.hom := sorry

/-- The source cell of the inverse morphism constructed by `iso₂Mk` is the
inverse cell of the supplied source-map isomorphism. -/
@[simp]
theorem iso₂Mk_inv_map₂
    {S T : ColaxCostructuredArrow K X} {f g : S ⟶ T}
    (e : ColaxCostructuredArrow.map f ≅
      ColaxCostructuredArrow.map g)
    (comm :
      (T.comparison S.left).map e.hom ≫
          ColaxCostructuredArrow.fac g =
        ColaxCostructuredArrow.fac f) :
    ColaxCostructuredArrow.map₂ (iso₂Mk e comm).inv =
      e.inv := sorry

/- Data and axiom audit (mathlib 4.32):

Both cells of `iso₂Mk` are built by `ColaxCostructuredArrow.hom₂Mk` from the
explicit `e.hom` and `e.inv`. The inverse compatibility and inverse laws are
`Prop`-valued fields; no source cell or endpoint datum is selected through a
proof placeholder. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
