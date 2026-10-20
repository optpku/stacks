/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Criterion
import StacksCheckRecall

@[expose] public section

/-!
# A slice-presheaf criterion for stacks in groupoids

The canonical statement uses `FiberedCategoryOver.Groupoids.baseChange`; no chapter-local slice
two-fibre-product owner is introduced.
-/

namespace CategoryTheory

/- Lemma 8.6.11: fiberwise faithfulness and the slice iso-class sheaf condition reflect the
stack-in-groupoids property from the target. The reusable statement allows the two total
categories to live in independent universes. -/
@[stacks 0CKJ]
#check @IsStack.InGroupoids.ofCartesianFiberFaithful

/- Total faithfulness is equivalent to the source's fiberwise hypothesis at the neutral
cartesian-functor layer and gives a direct companion criterion. -/
#check @CartesianBasedFunctor.faithful_iff_fiberwise
#check @IsStack.InGroupoids.ofCartesianFaithful

/- The fixed bicategorical owner remains as an application-facing specialization. -/
#check @IsStack.InGroupoids.ofFiberFaithful
#check @IsStack.InGroupoids.ofFaithful

/- The source's dependent family of sheaf hypotheses is available at both abstraction layers. -/
#check @CartesianBasedFunctor.fiberPairClasses.isSheaf
#check @FiberedCategoryOver.Groupoids.Hom.fiberPairClasses.isSheaf

/- The representation-independent all-slice formulation and its exact Yoneda bridge remain
available for downstream arguments that naturally start from a slice morphism. -/
#check @FiberedCategoryOver.Groupoids.Hom.fiberPairClasses.isSheaf_iff_slice
#check @IsStack.InGroupoids.ofFiberFaithful.slices
#check @IsStack.InGroupoids.ofCartesianFaithful.slices
#check @IsStack.InGroupoids.ofFaithful.slices

end CategoryTheory
