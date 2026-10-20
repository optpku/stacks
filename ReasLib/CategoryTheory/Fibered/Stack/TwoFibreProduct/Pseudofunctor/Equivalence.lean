/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of stack-valued two-fibre products

This leaf specializes the canonical pseudofunctorial equivalence and exposes its forward,
inverse, unit, and counit components at the groupoid-stack layer.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- A bicategorical equivalence of bundled cospans of groupoid stacks induces the canonical
equivalence of their stack-valued two-fibre products. -/
@[stacks 02ZL "equivalence induced on groupoid-stack two-fibre products"]
noncomputable def mapEquivalence (e : S ≌ T) :
    (pseudofunctor J).obj S ≌ (pseudofunctor J).obj T :=
  (pseudofunctor J).mapEquivalence e

/-- The forward morphism of the induced equivalence is the direct two-fibre-product map. -/
@[simp, stacks 02ZL "forward map of a groupoid-stack two-fibre-product equivalence"]
theorem mapEquivalence.hom (e : S ≌ T) :
    (mapEquivalence e).hom = map e.hom := sorry

/-- The inverse morphism of the induced equivalence is the direct two-fibre-product map. -/
@[simp, stacks 02ZL "inverse map of a groupoid-stack two-fibre-product equivalence"]
theorem mapEquivalence.inv (e : S ≌ T) :
    (mapEquivalence e).inv = map e.inv := sorry

/-- The unit of the induced equivalence is the canonical pseudofunctorial unit. -/
@[simp, stacks 02ZL "unit of a groupoid-stack two-fibre-product equivalence"]
theorem mapEquivalence.unit (e : S ≌ T) :
    (mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor J) e := sorry

/-- The counit is the canonical pseudofunctorial counit; heterogeneous equality records only
the proof-bearing endpoint presentation of the full-sub lift. -/
@[stacks 02ZL "counit of a groupoid-stack two-fibre-product equivalence"]
theorem mapEquivalence.counit (e : S ≌ T) :
    (mapEquivalence e).counit ≍
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor J) e := sorry

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
