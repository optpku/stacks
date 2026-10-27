/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Inclusion
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Precoverage.Cocontinuous

/-! Selected covering properties of the lisse-étale and flat-fppf inclusions. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The lisse-étale inclusion preserves selected covering families of the
lisse-étale precoverage. -/
instance lisseEtaleInclusion.instPrecoverageIsContinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsContinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage :=
  sorry

/-- The lisse-étale inclusion is cocontinuous for selected covering families. -/
instance lisseEtaleInclusion.instPrecoverageIsCocontinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsCocontinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage :=
  sorry

/-- The flat-fppf inclusion preserves selected covering families of the
flat-fppf precoverage. -/
instance flatFppfInclusion.instPrecoverageIsContinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsContinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage :=
  sorry

/-- The flat-fppf inclusion is cocontinuous for selected covering families. -/
instance flatFppfInclusion.instPrecoverageIsCocontinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsCocontinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage :=
  sorry

end AlgebraicGeometry.AlgebraicStack
