/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of set-stack two-fibre products

This leaf specializes the canonical pseudofunctorial equivalence and exposes its four
computational components at the set-stack layer.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- A bicategorical equivalence of set-stack cospans induces the canonical equivalence of
their two-fibre products. -/
@[stacks 0434 "set-stack two-fibre-product equivalence action"]
noncomputable def mapEquivalence (e : S ≌ T) :
    (pseudofunctor J).obj S ≌ (pseudofunctor J).obj T :=
  (pseudofunctor J).mapEquivalence e

/-- The forward morphism of the induced equivalence is the direct map. -/
@[simp, stacks 0434 "set-stack two-fibre-product equivalence forward readout"]
theorem mapEquivalence.hom (e : S ≌ T) :
    (mapEquivalence e).hom = map e.hom := sorry

/-- The inverse morphism of the induced equivalence is the direct map. -/
@[simp, stacks 0434 "set-stack two-fibre-product equivalence inverse readout"]
theorem mapEquivalence.inv (e : S ≌ T) :
    (mapEquivalence e).inv = map e.inv := sorry

/-- The unit is the canonical pseudofunctorial unit of the mapped equivalence. -/
@[simp, stacks 0434 "set-stack two-fibre-product equivalence unit readout"]
theorem mapEquivalence.unit (e : S ≌ T) :
    (mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor J) e := sorry

/-- The counit is the canonical pseudofunctorial counit; heterogeneous equality records only
the proof-bearing endpoint presentation of the full-sub lift. -/
@[stacks 0434 "set-stack two-fibre-product equivalence counit readout"]
theorem mapEquivalence.counit (e : S ≌ T) :
    (mapEquivalence e).counit ≍
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor J) e := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
