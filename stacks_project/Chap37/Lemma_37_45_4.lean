/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Filtration
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.45.4: a flat, locally finitely presented, separated, quasi-finite morphism admits
an increasing exhaustive closed degree filtration whose strata universally classify finite
locally free base changes and whose canonical inclusions are quasi-compact. -/
@[stacks 07RZ] #check
  (AlgebraicGeometry.Scheme.Hom.exists_degreeFiltration :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.Scheme.Hom.QuasiFinite f],
      Nonempty (AlgebraicGeometry.Scheme.Hom.DegreeFiltration f))
