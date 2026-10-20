/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections.CupProduct
public import ReasLib.CategoryTheory.Monoidal.CohomologyProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor
open AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport
open scoped RingedSpaceTensor
open scoped RingedSpaceDerivedGlobalSections
open scoped RingedSpaceClosedSupport

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {Z : TopologicalSpace.Closeds X}
variable [ModuleDerived.Tensor.Has X]

namespace ClosedSubset.CupProduct

/- Lemma 20.34.11: the supported cohomology product commutes with forgetting support in degrees
`i` and `j`.  The reusable family-level owner stores the ambient realization and its
forget-support square, while `SupportedCupProduct.cohomologyCommSq` exposes the source-facing
graded square. -/
@[stacks 0G77 "Lemma 20.34.11 supported cohomology square"]
#check @SupportedCupProduct.cohomologyCommSq

#check @SupportedCupProduct.derivedCommSq

end ClosedSubset.CupProduct

end

end AlgebraicGeometry.RingedSpace
