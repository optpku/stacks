/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.Equivalence
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Comparison
import StacksCheckRecall

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{vS, uS} C}
variable (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p]
variable (U : C)
variable (Z : FiberedCategoryOver.Setoids C)

/- Lemma 4.39.5 (1): a category equivalent over the base to one fibred in sets is fibred in
setoids. -/
@[stacks 0045 "(1)"]
#check (BasedCategory.Equivalence.inSetoids.of_targetDiscrete e :
  Functor.IsFibered.InSetoids X.p)

/- Lemma 4.39.5 (2): an equivalence to a discrete fibration induces a bijection from fibrewise
isomorphism classes to target-fibre objects. -/
@[stacks 0045 "(2)"]
#check (BasedCategory.Equivalence.fiberIsoClasses.bijective e U :
  Function.Bijective (e.hom.fiberFunctor U).isoClassesToObj)

/- The reusable data form of (2) packages the forward map and its explicit inverse. -/
#check (BasedCategory.Equivalence.fiberIsoClasses.equiv e U :
  isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U)

/- Lemma 4.39.5 (3): the canonical comparison with the associated category fibred in sets is an
equivalence over the base. -/
@[stacks 0045 "(3)"]
#check (FiberedCategoryOver.Setoids.toAssociatedSets.exists_equivalence Z :
  ∃ e : Z.toBasedCategory ≌ Z.associatedSets.toBasedCategory,
    e.hom = FiberedCategoryOver.Setoids.toBasedFunctor Z.toAssociatedSets)

end CategoryTheory
