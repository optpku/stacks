/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyClosedReduction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace TopologicalSpace CategoryTheory

universe u

/- Remark 67.12.5: a locally closed subset `T ⊂ Points X` of an algebraic space
`X` over a scheme `S` has a reduced induced subspace structure, obtained as the
reduced closed subspace of the open subspace `U` with
`U.pointsSet = Points X \ ∂T`, where `∂T = closure T \ T`. -/
@[stacks 06EC] #check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedReduction.spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (T : LocallyCloseds (Points X)),
    (LocallyClosedReduction.ambientOpen T).pointsSet = (LocallyClosedReduction.boundary T)ᶜ ∧
      IsOpenImmersion (LocallyClosedReduction.ambientOpen T).ι ∧
      IsClosedImmersion (LocallyClosedReduction.ιToAmbientOpen T) ∧
      IsImmersion (LocallyClosedReduction.ι T) ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (LocallyClosedReduction.space T) ∧
      Set.range (Points.map (LocallyClosedReduction.ι T)) = (T : Set (Points X)))
