/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.RingTheory.FiniteFree

/-!
# Finite locally free scheme morphisms

This file owns the basic scheme-morphism property of being affine with finite
locally free pushforward structure sheaf.  The module condition itself is
owned by the generic ringed-site API.
-/

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/-- The direct image of the structure sheaf, viewed as a module on the target scheme. -/
noncomputable def pushforwardStructureModule (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit X.ringCatSheaf : X.Modules)

end Scheme.Hom

/-- A scheme morphism is finite locally free when it is affine and its pushforward structure
sheaf is finite locally free on the target. -/
class IsFiniteLocallyFree (f : X ⟶ S) : Prop extends IsAffineHom f where
  /-- The pushforward structure sheaf is finite locally free. -/
  pushforward_isFiniteLocallyFree :
    Scheme.Modules.IsFiniteLocallyFree f.pushforwardStructureModule

/-- A finite locally free morphism supplies finite local freeness of its pushforward structure
sheaf to typeclass search. -/
instance IsFiniteLocallyFree.pushforwardStructureModule
    (f : X ⟶ S) [h : IsFiniteLocallyFree f] :
    Scheme.Modules.IsFiniteLocallyFree f.pushforwardStructureModule := sorry

/-- A morphism is finite locally free exactly when it is affine and its pushforward structure
sheaf is finite locally free. -/
theorem isFiniteLocallyFree_iff (f : X ⟶ S) :
    IsFiniteLocallyFree f ↔
      IsAffineHom f ∧ Scheme.Modules.IsFiniteLocallyFree f.pushforwardStructureModule := sorry

/-- A finite locally free morphism has rank `d` when its pushforward structure sheaf has constant
finite local rank `d`. -/
class IsFiniteLocallyFreeOfRank (f : X ⟶ S) (d : ℕ) : Prop extends IsFiniteLocallyFree f where
  /-- The pushforward structure sheaf has rank `d`. -/
  pushforward_isFiniteLocallyFreeOfRank :
    Scheme.Modules.IsFiniteLocallyFreeOfRank d f.pushforwardStructureModule

/-- A finite locally free morphism of rank `d` supplies fixed finite local rank of its pushforward
structure sheaf to typeclass search. -/
instance IsFiniteLocallyFreeOfRank.pushforwardStructureModule
    (f : X ⟶ S) (d : ℕ) [h : IsFiniteLocallyFreeOfRank f d] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank d f.pushforwardStructureModule := sorry

/-- A morphism is finite locally free of rank `d` exactly when it is finite locally free and its
pushforward structure sheaf has rank `d`. -/
theorem isFiniteLocallyFreeOfRank_iff (f : X ⟶ S) (d : ℕ) :
    IsFiniteLocallyFreeOfRank f d ↔
      IsFiniteLocallyFree f ∧
        Scheme.Modules.IsFiniteLocallyFreeOfRank d f.pushforwardStructureModule := sorry

end

end AlgebraicGeometry
