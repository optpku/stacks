/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic

/-!
# Discrete fibrations as setoid fibrations

The canonical bridge from strict unique lifting to the equivalence-invariant thin-fiber layer.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsDiscreteFibration

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- Every discrete fibration is canonically fibred in setoids. -/
instance inSetoids (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    Functor.IsFibered.InSetoids p := sorry

end CategoryTheory.Functor.IsDiscreteFibration
