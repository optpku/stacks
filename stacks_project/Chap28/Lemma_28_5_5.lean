/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Noetherian.Topology
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.5.5 (1): a locally Noetherian scheme has a locally Noetherian underlying
topological space. -/
@[stacks 01OZ] #check
  (AlgebraicGeometry.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsLocallyNoetherian X] →
      TopologicalSpace.LocallyNoetherianSpace X)

/- Lemma 28.5.5 (2): a Noetherian scheme has a Noetherian underlying topological space. -/
@[stacks 01OZ] #check (AlgebraicGeometry.IsNoetherian.noetherianSpace :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsNoetherian X] →
    TopologicalSpace.NoetherianSpace X)
