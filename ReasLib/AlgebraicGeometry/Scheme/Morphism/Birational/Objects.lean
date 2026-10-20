/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Birational Relations Between Schemes

This leaf contains the object-level formulations of birationality in terms of
function fields and generic-point schemes over a base.  It complements the
morphism-level `IsBirational` predicate without choosing a particular
birational morphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Two irreducible schemes are birational when their function fields are
isomorphic as commutative rings. -/
def Birational (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic X.functionField Y.functionField

/-- Birationality of irreducible schemes is symmetric. -/
theorem Birational.symm {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y] :
    Birational X Y → Birational Y X := sorry

/-- Birationality of irreducible schemes is a symmetric relation. -/
theorem birational_comm (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] :
    Birational X Y ↔ Birational Y X := sorry

/-- The generic-point scheme of an irreducible scheme over `S`, regarded as an
object of the over category of `S`. -/
noncomputable abbrev genericPointOver
    (S X : Scheme) [X.Over S] [IrreducibleSpace X] : Over S :=
  Over.mk (X.fromSpecStalk (genericPoint X) ≫ (X ↘ S))

/-- Two irreducible schemes over `S` are birational over `S` when their
generic-point schemes are isomorphic in `Over S`. -/
def BirationalOver (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic (genericPointOver S X) (genericPointOver S Y)

/-- Birationality over a base is symmetric. -/
theorem BirationalOver.symm {S X Y : Scheme} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y → BirationalOver S Y X := sorry

/-- Birationality over a base is a symmetric relation. -/
theorem birationalOver_comm (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y ↔ BirationalOver S Y X := sorry

end AlgebraicGeometry
