/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison computations for fixed-base pullback on stacks

This leaf exposes both directions of the identity and composition comparisons after forgetting
the stack condition, and records the pseudofunctor-level factorization through the ambient
fixed-base pullback.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace StackOver.Pullback

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- The forward identity comparison of stack pullback forgets to that of the ambient-valued
pullback pseudofunctor. -/
@[simp, stacks 04WC "stack-pullback identity comparison forward ambient readout"]
theorem pseudofunctor.mapId.hom.toAmbient (T : StackOver.{uD, vD, uS, vS} K) :
    ((pseudofunctor J K u).mapId T).hom.hom =
      ((ambient K u).mapId T).hom := sorry

/-- The inverse identity comparison of stack pullback forgets to that of the ambient-valued
pullback pseudofunctor. -/
@[simp, stacks 04WC "stack-pullback identity comparison inverse ambient readout"]
theorem pseudofunctor.mapId.inv.toAmbient (T : StackOver.{uD, vD, uS, vS} K) :
    ((pseudofunctor J K u).mapId T).inv.hom =
      ((ambient K u).mapId T).inv := sorry

/-- The forward composition comparison of stack pullback forgets to that of the ambient-valued
pullback pseudofunctor. -/
@[simp, stacks 04WC "stack-pullback composition comparison forward ambient readout"]
theorem pseudofunctor.mapComp.hom.toAmbient
    {X Y Z : StackOver.{uD, vD, uS, vS} K}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor J K u).mapComp F G).hom.hom =
      ((ambient K u).mapComp F G).hom := sorry

/-- The inverse composition comparison of stack pullback forgets to that of the ambient-valued
pullback pseudofunctor. -/
@[simp, stacks 04WC "stack-pullback composition comparison inverse ambient readout"]
theorem pseudofunctor.mapComp.inv.toAmbient
    {X Y Z : StackOver.{uD, vD, uS, vS} K}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor J K u).mapComp F G).inv.hom =
      ((ambient K u).mapComp F G).inv := sorry

/-- Forgetting the stack condition after fixed-base pullback recovers the ambient-valued
pullback pseudofunctor, including its `1`-cell, `2`-cell, and comparison data. -/
@[stacks 04WC "stack-pullback pseudofunctor forgetful factorization"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J K u).comp
        (StackOver.forget J).toPseudofunctor =
      ambient K u := sorry

end StackOver.Pullback

end CategoryTheory
