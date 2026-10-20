/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids.Criterion
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# A slice-presheaf criterion for stacks in groupoids

The source condition is indexed by fiber objects and expressed through the canonical
bicategorical base change `FiberedCategoryOver.Groupoids.baseChange`. Fibered Yoneda identifies it
with the representation-independent condition over all slice morphisms, without introducing a
second slice-product carrier.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids.Hom

/-- Every slice base change of `F` has a sheaf of fiberwise isomorphism classes. -/
@[stacks 0CKJ "slice fiber-class sheaf criterion"]
def sliceFiberClasses.isSheaf
    (J : GrothendieckTopology C) (F : X ⟶ T) : Prop :=
  CartesianBasedFunctor.sliceFiberClasses.isSheaf J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- The source-facing 0CKJ condition: every target-fiber object admits a slice representative
whose base-change fiber-class presheaf is a sheaf on the slice site. -/
@[stacks 0CKJ "fiber-pair sheaf criterion for a cartesian functor"]
def fiberPairClasses.isSheaf
    (J : GrothendieckTopology C) (F : X ⟶ T) : Prop :=
  CartesianBasedFunctor.fiberPairClasses.isSheaf J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- The named all-slice condition unfolds to the sheaf condition for every slice base change. -/
@[stacks 0CKJ "slice fiber-class criterion expansion"]
theorem sliceFiberClasses.isSheaf_iff
    (J : GrothendieckTopology C) (F : X ⟶ T) :
    sliceFiberClasses.isSheaf J F ↔
      ∀ ⦃U : C⦄ (G : FiberedCategoryOver.Groupoids.slice U ⟶ T),
        Presheaf.IsSheaf (J.over U) (sliceFiberClasses F G) := sorry

/-- The named fiber-pair condition unfolds to the sheaf condition for each concrete fiber-pair
presheaf. -/
@[stacks 0CKJ "fiber-pair criterion expansion"]
theorem fiberPairClasses.isSheaf_iff
    (J : GrothendieckTopology C) (F : X ⟶ T) :
    fiberPairClasses.isSheaf J F ↔
      ∀ ⦃U : C⦄ (y : T.p.Fiber U),
        Presheaf.IsSheaf (J.over U) (fiberPairClasses F y) := sorry

/-- Fibered Yoneda identifies the source-facing fiber-object condition with the condition for
all morphisms from canonical slice fibrations. -/
@[stacks 0CKJ "fiber-pair and slice fiber-class criterion equivalence"]
theorem fiberPairClasses.isSheaf_iff_slice
    (J : GrothendieckTopology C) (F : X ⟶ T) :
    fiberPairClasses.isSheaf J F ↔
      sliceFiberClasses.isSheaf J F := sorry

end FiberedCategoryOver.Groupoids.Hom

namespace IsStack.InGroupoids

/-- Fixed-owner specialization of the universe-polymorphic fiber-faithful stack criterion. -/
@[stacks 0CKJ "fiberwise-faithful stack criterion in groupoids"]
theorem ofFiberFaithful
    (F : X ⟶ T) [IsStack.InGroupoids J T.p]
    (hFaithful : ∀ U : C, (FiberedCategoryOver.Groupoids.fiberFunctor F U).Faithful)
    (hSheaf :
      FiberedCategoryOver.Groupoids.Hom.fiberPairClasses.isSheaf J F) :
    IsStack.InGroupoids J X.p := sorry

/-- The representation-independent all-slice condition gives the same stack-in-groupoids
criterion. This is the generalized companion to the source-facing 0CKJ statement. -/
@[stacks 0CKJ "slice-form fiberwise-faithful stack criterion"]
theorem ofFiberFaithful.slices
    (F : X ⟶ T) [IsStack.InGroupoids J T.p]
    (hFaithful : ∀ U : C, (FiberedCategoryOver.Groupoids.fiberFunctor F U).Faithful)
    (hSheaf :
      FiberedCategoryOver.Groupoids.Hom.sliceFiberClasses.isSheaf J F) :
    IsStack.InGroupoids J X.p := sorry

/-- Faithfulness of the total based functor and the source-facing fiber-pair sheaf condition
reflect the stack-in-groupoids property from the target. -/
@[stacks 0CKJ "faithful stack criterion in groupoids"]
theorem ofFaithful
    (F : X ⟶ T) [IsStack.InGroupoids J T.p]
    (hFaithful : (FiberedCategoryOver.Groupoids.toBasedFunctor F).Faithful)
    (hSheaf :
      FiberedCategoryOver.Groupoids.Hom.fiberPairClasses.isSheaf J F) :
    IsStack.InGroupoids J X.p := sorry

/-- Faithfulness of the total based functor and the representation-independent all-slice sheaf
condition reflect the stack-in-groupoids property from the target. -/
@[stacks 0CKJ "slice-form faithful stack criterion in groupoids"]
theorem ofFaithful.slices
    (F : X ⟶ T) [IsStack.InGroupoids J T.p]
    (hFaithful : (FiberedCategoryOver.Groupoids.toBasedFunctor F).Faithful)
    (hSheaf :
      FiberedCategoryOver.Groupoids.Hom.sliceFiberClasses.isSheaf J F) :
    IsStack.InGroupoids J X.p := sorry

end IsStack.InGroupoids

end CategoryTheory
