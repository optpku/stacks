/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry
open AlgebraicGeometry

universe u

/- Definition 29.51.12: for integral schemes `X` and `Y`, an alteration `f : Y ⟶ X` is a
proper dominant morphism whose restriction over some nonempty open of `X` is finite. -/
@[stacks 0AB0] #check (@AlgebraicGeometry.isAlteration_iff :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : Y ⟶ X),
    AlgebraicGeometry.IsAlteration f ↔
      AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.IsDominant f ∧
        ∃ U : X.Opens, Nonempty U ∧ AlgebraicGeometry.IsFinite (f ∣_ U))

#check (AlgebraicGeometry.IsAlteration :
  ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y], (Y ⟶ X) → Prop)
