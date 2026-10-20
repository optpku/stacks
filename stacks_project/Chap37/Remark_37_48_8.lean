/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 37.48.8: the identity on `Over S` induces the comparison morphism
from the big ph topos to the big fppf topos. -/
@[stacks 0DBU] #check
  (AlgebraicGeometry.Scheme.PhComparison.epsilon :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      MorphismOfTopoiIn (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.Scheme.bigPhSite S))

/- The underlying identity functor is a morphism of sites in the required direction. -/
#check AlgebraicGeometry.Scheme.PhComparison.identity_isMorphismOfSites

/- Direct image preserves the underlying presheaf. -/
#check AlgebraicGeometry.Scheme.PhComparison.epsilon_pushforward_val

/- Inverse image is canonically ph sheafification. -/
#check AlgebraicGeometry.Scheme.PhComparison.epsilonInverseImageIsoSheafification

/- Composition gives the ph comparisons with all five standard topologies. -/
#check AlgebraicGeometry.Scheme.PhComparison.standardComparison
