/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Copower

/-!
# Copowers and objectwise coskeletons

A right Kan extension from truncated simplicial degrees turns maps from a constant copower
indexed by `K` into maps from the copower indexed by `sk n K`.  The universal-property layer
accepts any explicit right Kan presentation; the chosen-coskeleton layer specializes it using
the canonical presentation supplied by `SimplicialObject.Truncated.coskeleton`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.copower

variable {C : Type u} [Category.{v} C]

namespace truncation

/-- Maps from a constant copower into any right Kan extension of `(truncation n).obj V` are
equivalently maps from the skeleton-indexed copower into `V`. -/
@[stacks 018V "copowers into a right Kan extension"]
noncomputable def rightKanHomEquiv (n : ℕ) (K : SSet.{w})
    (V : SimplicialObject C) {W : SimplicialObject C}
    (ε : (SimplexCategory.Truncated.inclusion n).op ⋙ W ⟶ (truncation n).obj V)
    [W.IsRightKanExtension ε] (X : C)
    [HasCopower K ((const C).obj X)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj X)] :
    (copower K ((const C).obj X) ⟶ W) ≃
      (copower ((SSet.sk n).obj K) ((const C).obj X) ⟶ V) :=
  (W.homEquivOfIsRightKanExtension ε
      (copower K ((const C).obj X))).trans
    (skeletonHomEquiv n K X V)

/-- The copower equivalence for an explicit right Kan presentation is contravariantly natural
in the constant object. -/
@[stacks 018V "right-Kan copower equivalence naturality"]
theorem rightKanHomEquiv.precomp (n : ℕ) (K : SSet.{w})
    (V : SimplicialObject C) {W : SimplicialObject C}
    (ε : (SimplexCategory.Truncated.inclusion n).op ⋙ W ⟶ (truncation n).obj V)
    [W.IsRightKanExtension ε] {X Y : C}
    [HasCopower K ((const C).obj X)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj X)]
    [HasCopower K ((const C).obj Y)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj Y)]
    (f : X ⟶ Y) (g : copower K ((const C).obj Y) ⟶ W) :
    rightKanHomEquiv n K V ε X
        (copower.hom K ((const C).map f) ≫ g) =
      copower.hom ((SSet.sk n).obj K) ((const C).map f) ≫
        rightKanHomEquiv n K V ε Y g := sorry

end truncation

namespace coskeleton

/-- Maps from a constant copower into the chosen objectwise coskeleton are equivalently maps
from the skeleton-indexed copower into the original simplicial object. -/
@[stacks 018V "copowers into an objectwise coskeleton"]
noncomputable def homEquiv (n : ℕ) (K : SSet.{w})
    (V : SimplicialObject C) (X : C)
    [HasCopower K ((const C).obj X)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj X)]
    [((truncation n).obj V).HasCoskeleton] :
    (copower K ((const C).obj X) ⟶ ((truncation n).obj V).coskeleton) ≃
      (copower ((SSet.sk n).obj K) ((const C).obj X) ⟶ V) :=
  truncation.rightKanHomEquiv n K V
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit
      ((truncation n).obj V)) X

/-- The copower-to-coskeleton equivalence is contravariantly natural in the constant object. -/
@[stacks 018V "copower-to-coskeleton naturality"]
theorem homEquiv.precomp (n : ℕ) (K : SSet.{w})
    (V : SimplicialObject C) [((truncation n).obj V).HasCoskeleton]
    {X Y : C}
    [HasCopower K ((const C).obj X)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj X)]
    [HasCopower K ((const C).obj Y)]
    [HasCopower ((SSet.sk n).obj K) ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : copower K ((const C).obj Y) ⟶ ((truncation n).obj V).coskeleton) :
    homEquiv n K V X (copower.hom K ((const C).map f) ≫ g) =
      copower.hom ((SSet.sk n).obj K) ((const C).map f) ≫
        homEquiv n K V Y g := sorry

end coskeleton

end CategoryTheory.SimplicialObject.copower
