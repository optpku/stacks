/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cone computations for two-fibre products of stacks in sets

This leaf exposes the comparison and cone fields and installs the bilimit instances. The direct
carrier, projection, comparison, and cone data remain in `TwoFibreProduct.Basic`.
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

variable {X Y S :
  StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J}

/-- Forgetting discreteness from the forward comparison cell recovers the setoid-stack
comparison cell. -/
@[simp, stacks 0434 "set-stack two-fibre-product comparison forward readout"]
theorem comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).hom.hom =
      (StackOver.Setoids.TwoFibreProduct.comparisonIso
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).hom := sorry

/-- Forgetting discreteness from the inverse comparison cell recovers the inverse setoid-stack
comparison cell. -/
@[simp, stacks 0434 "set-stack two-fibre-product comparison inverse readout"]
theorem comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).inv.hom =
      (StackOver.Setoids.TwoFibreProduct.comparisonIso
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).inv := sorry

/-- The apex of the canonical set-valued stack cone is the explicit two-fibre product. -/
@[simp, stacks 0434 "set-stack two-fibre-product cone apex readout"]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the canonical set-valued stack cone is its first projection. -/
@[simp, stacks 0434 "set-stack two-fibre-product cone first leg readout"]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the canonical set-valued stack cone is its second projection. -/
@[simp, stacks 0434 "set-stack two-fibre-product cone second leg readout"]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the canonical set-valued stack cone is its comparison
isomorphism. -/
@[simp, stacks 0434 "set-stack two-fibre-product cone comparison readout"]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

/-- The canonical cone of stacks in sets is a bilimit. -/
@[stacks 0434 "set-stack two-fibre-product bilimit cone"]
instance cone.isBilimit (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry

end StackOver.Sets.TwoFibreProduct

namespace StackOver.Sets

/-- The bicategory of stacks in sets over a site has pseudo-pullbacks. -/
@[stacks 0434 "two-fibre products of stacks in sets"]
instance hasPseudoPullbacks : Bicategory.HasPseudoPullbacks (StackOver.Sets J) := sorry

end StackOver.Sets

end CategoryTheory
