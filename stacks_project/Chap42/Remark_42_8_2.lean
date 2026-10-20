/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.Pointwise
public import stacks_project.Chap42.Situation_42_7_1
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.CycleGroup

universe u

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Remark 42.8.2: under Situation 42.7.1, the group of `k`-cycles is the subgroup
of locally finite degree-zero Milnor K-coefficient families at points of relative
dimension `k`. The ambient dependent product permits infinite global support, as
required by the primed-sum convention: only the nonzero coefficients in each
quasi-compact open are required to form a finite set. -/
@[stacks 0GU2] #check (AlgebraicGeometry.CycleGroup.Pointwise.equiv
  (f.relativeDimensionFunction δ) k :
    CycleGroup X (f.relativeDimensionFunction δ) k ≃+
      AlgebraicGeometry.CycleGroup.Pointwise.locallyFinite (f.relativeDimensionFunction δ) k)

/- The identification sends each integer cycle coefficient through `degreeZeroMap`. -/
#check (AlgebraicGeometry.CycleGroup.Pointwise.equiv_apply (f.relativeDimensionFunction δ) k :
  ∀ (α : CycleGroup X (f.relativeDimensionFunction δ) k)
    (x : {x : X // f.relativeDimensionFunction δ x = k}),
    (Pointwise.equiv (f.relativeDimensionFunction δ) k α).1 x =
      MilnorK.degreeZeroMap (X.residueField x.1)
        (toAlgebraicCycle (f.relativeDimensionFunction δ) k α x.1))

#check ((Pointwise.locallyFinite (f.relativeDimensionFunction δ) k).subtype :
  Pointwise.locallyFinite (f.relativeDimensionFunction δ) k →+
    Pointwise.Coefficients (f.relativeDimensionFunction δ) k)
