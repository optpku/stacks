/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.Stratification
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.1: a scheme-to-algebraic-space morphism that is flat, locally of finite
presentation, separated, locally quasi-finite, and has universally bounded fibres admits a
finite nested family of reduced closed subspaces whose successive differences classify finite
locally free base changes by rank. -/
@[stacks 07S8] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_degreeStratification :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S} (f : ofOver W ⟶ X)
      [Flat f] [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f],
      universallyBoundedFibres f → Nonempty (DegreeStratification f))

#check AlgebraicGeometry.AlgebraicSpace.DegreeStratification
#check AlgebraicGeometry.AlgebraicSpace.DegreeStratification.pullbackRank_iff

end AlgebraicSpace
end AlgebraicGeometry
