/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.8.3: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. An alteration of `X` is a proper dominant morphism `f : Y ⟶ X` of
algebraic spaces over `S` with `Y` integral such that `f⁻¹(U) ⟶ U` is finite
for some nonempty open `U ⊂ X`. -/
@[stacks 0ADA] #check (AlgebraicGeometry.AlgebraicSpace.IsAlteration :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} [IsIntegral Y] [IsIntegral X],
    (Y ⟶ X) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.isAlteration_iff :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X),
    IsAlteration f ↔
      Proper f ∧ Dominant f ∧
        ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
          IsFinite (pullback.snd f U.ι))
