/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.AlgebraicTopology.SimplicialSet.Objwise
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Skeleton.Degreewise
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness and nonemptiness of simplicial skeletons

The primary finiteness instance is stated for the left extension of a truncated simplicial set.
The full skeleton has a low-priority presentation bridge because typeclass search does not unfold
through Mathlib's bundled `SSet.sk` composition far enough to reuse the primary instance directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Truncated.skeleton.degree
open scoped Simplicial

noncomputable section

universe w

namespace SSet.Truncated

/-- Left extension along the truncated simplex-category inclusion preserves objectwise
finiteness. -/
@[stacks 018V "skeleton preserves degreewise finiteness"]
instance sk.objFinite {n : ℕ} (U : SSet.Truncated.{w} n) [U.ObjFinite] :
    ((Truncated.sk n).obj U).ObjFinite where
  finite Delta :=
    Finite.of_equiv (colimit (diagram U Delta.unop))
      (h := FintypeCat.finite_of_isColimit (colimit.isColimit _))
      (Iso.toEquiv (isoColimit U Delta.unop).symm)

end SSet.Truncated

namespace SSet

/-- Truncation preserves objectwise finiteness. This named bridge exposes the generic
precomposition instance without requiring typeclass search to unfold `SSet.truncation`. -/
@[stacks 017E "truncation preserves degreewise finiteness"]
instance truncation.objFinite (n : ℕ) (U : SSet.{w}) [U.ObjFinite] :
    ((truncation n).obj U).ObjFinite :=
  CategoryTheory.Functor.ObjFinite.comp
    (SimplexCategory.Truncated.inclusion n).op U

/-- The full simplicial skeleton of an objectwise finite simplicial set is objectwise finite.
This low-priority presentation bridge exposes the canonical truncated-skeleton result through
Mathlib's bundled `SSet.sk`; it does not introduce a second mathematical construction. -/
@[stacks 018V "full skeleton preserves degreewise finiteness"]
instance (priority := 40) sk.objFinite (n : ℕ) (U : SSet.{w}) [U.ObjFinite] :
    ((sk n).obj U).ObjFinite :=
  SSet.Truncated.sk.objFinite ((truncation n).obj U)

/-- Skeleton preserves the existence of a vertex. -/
@[stacks 018V "skeleton preserves nonemptiness"]
instance sk.nonempty (n : ℕ) (U : SSet.{w}) [U.Nonempty] :
    ((sk n).obj U).Nonempty :=
  Nonempty.map
    (((skAdj n).unit.app ((truncation n).obj U)).app
      (op (⟨SimplexCategory.mk 0, Nat.zero_le n⟩ : SimplexCategory.Truncated n)))
    (inferInstance : U.Nonempty)

end SSet
