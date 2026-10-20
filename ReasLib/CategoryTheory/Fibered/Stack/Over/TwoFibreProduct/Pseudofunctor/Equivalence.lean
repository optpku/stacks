/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of stack-valued two-fibre products

An equivalence of bundled cospans induces the canonical equivalence of their stack-valued
two-fibre-product apices, with direct readouts of both maps, the unit, and the counit.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- A bicategorical equivalence of bundled cospans of stacks induces the canonical equivalence of
their stack-valued two-fibre products. -/
@[stacks 026G "stack two-fibre-product equivalence action"]
noncomputable def mapEquivalence (e : S ≌ T) :
    (pseudofunctor J).obj S ≌ (pseudofunctor J).obj T :=
  (pseudofunctor J).mapEquivalence e

/-- The forward morphism of the induced equivalence is the public two-fibre-product map. -/
@[simp, stacks 026G "stack two-fibre-product equivalence forward readout"]
theorem mapEquivalence.hom (e : S ≌ T) :
    (mapEquivalence e).hom = map e.hom := sorry

/-- The inverse morphism of the induced equivalence is the public two-fibre-product map. -/
@[simp, stacks 026G "stack two-fibre-product equivalence inverse readout"]
theorem mapEquivalence.inv (e : S ≌ T) :
    (mapEquivalence e).inv = map e.inv := sorry

/-- The unit of the induced equivalence is the canonical unit supplied by the stack-valued
two-fibre-product pseudofunctor. -/
@[simp, stacks 026G "stack two-fibre-product equivalence unit readout"]
theorem mapEquivalence.unit (e : S ≌ T) :
    (mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor J) e := sorry

/-- The counit of the induced equivalence is heterogeneously equal to the canonical counit
supplied by the stack-valued two-fibre-product pseudofunctor. The heterogeneous equality keeps
the definitionally equal full-subbicategory endpoints opaque. -/
@[stacks 026G "stack two-fibre-product equivalence counit readout"]
theorem mapEquivalence.counit (e : S ≌ T) :
    (mapEquivalence e).counit ≍
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor J) e := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
