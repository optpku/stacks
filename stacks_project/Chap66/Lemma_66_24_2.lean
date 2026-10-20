/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 66.24.2 (1): if an algebraic space `X` over a scheme `S` is locally Noetherian,
then `|X|` is a locally Noetherian topological space. -/
@[stacks 04ZF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [AlgebraicSpace.IsLocallyNoetherian X],
      TopologicalSpace.LocallyNoetherianSpace (AlgebraicSpace.Points X))

/- Lemma 66.24.2 (2): if an algebraic space `X` over a scheme `S` is quasi-compact and
locally Noetherian, then `|X|` is a Noetherian topological space. -/
@[stacks 04ZF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.noetherianSpace :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicSpace.IsQuasiCompact X] [AlgebraicSpace.IsLocallyNoetherian X],
      TopologicalSpace.NoetherianSpace (AlgebraicSpace.Points X))
