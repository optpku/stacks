/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Definition 21.17.13: derived tensor core

The reusable construction is owned by `DerivedCategory.DerivedTensor`.  For module sheaves on a
ringed site, `SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor` supplies the canonical
instance; this file only records the primitive source and derived-functor API used by the chapter.
-/

open CategoryTheory ComplexShape

/- Definition 21.17.13 (06YU): tensoring complexes of module sheaves has the canonical total
derived tensor construction. -/
@[stacks 06YU "derived tensor core"]
#check @SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor

#check @SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
#check @DerivedCategory.DerivedTensor.Right.sourceFunctorOfComplex
#check @DerivedCategory.DerivedTensor.Right.sourceFunctor
#check @DerivedCategory.DerivedTensor.Right.functor
#check @DerivedCategory.DerivedTensor.Right.obj
#check @DerivedCategory.DerivedTensor.Right.counit

end
