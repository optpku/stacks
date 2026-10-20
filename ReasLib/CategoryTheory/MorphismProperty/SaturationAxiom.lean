/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The saturation axiom for a morphism property

The saturation axiom is intrinsic to a morphism property: if the two adjacent composites in a
composable triple belong to the property, then so does the middle morphism.  It is independent of
any chosen localization model and of the stronger assumption that a calculus of fractions exists.

This file owns the primitive property and its basic transport instances.  The localization-based
closure operator belongs to `MorphismProperty.Saturation`.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The saturation axiom (MS4) for a morphism property: if the two adjacent composites among
three composable morphisms belong to `W`, then the middle morphism belongs to `W`.

This is kept independent of the calculus-of-fractions owners so constructions can reuse MS4
without manufacturing unrelated MS1--MS3 data. -/
@[stacks 05Q8 "saturated multiplicative systems"]
class HasSaturationAxiom (W : MorphismProperty C) : Prop where
  /-- The middle arrow belongs to `W` whenever its composites on both sides belong to `W`. -/
  mem_of_comp_mem {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
      (hfg : W (f ≫ g)) (hgh : W (g ≫ h)) : W g

/-- Isomorphisms satisfy the saturation axiom. -/
instance HasSaturationAxiom.isomorphisms : (isomorphisms D).HasSaturationAxiom := sorry
/- Proof strategy: the first invertible composite gives the middle arrow a left inverse, while
the second gives it a right inverse; the two inverses agree, so the middle arrow is invertible. -/

/-- The inverse image of a morphism property satisfying the saturation axiom also satisfies it. -/
instance HasSaturationAxiom.inverseImage (W : MorphismProperty D) [W.HasSaturationAxiom]
    (F : C ⥤ D) : (W.inverseImage F).HasSaturationAxiom := sorry
/- Proof strategy: rewrite both mapped composites using `F.map_comp`, apply saturation for `W`
to `F.map f`, `F.map g`, and `F.map h`, and unfold membership in `W.inverseImage F`. -/

/-- The saturation axiom is preserved by passing to the opposite morphism property. -/
instance HasSaturationAxiom.op (W : MorphismProperty C) [W.HasSaturationAxiom] :
    W.op.HasSaturationAxiom := sorry
/- Proof strategy: for composable `f`, `g`, and `h` in `Cᵒᵖ`, unop the two membership hypotheses
and apply `HasSaturationAxiom.mem_of_comp_mem` to `h.unop`, `g.unop`, and `f.unop`, with the two
hypotheses exchanged because opposite composition reverses their order. -/

/-- The saturation axiom is preserved by returning from an opposite morphism property. -/
instance HasSaturationAxiom.unop (W : MorphismProperty Cᵒᵖ) [W.HasSaturationAxiom] :
    W.unop.HasSaturationAxiom := sorry
/- Proof strategy: op the three arrows and the two composite-membership hypotheses, apply
`HasSaturationAxiom.mem_of_comp_mem` in `Cᵒᵖ` in reverse order, and use the definitional op-unop
identifications. -/


end MorphismProperty
end CategoryTheory
