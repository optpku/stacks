module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.PreservesLimits
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
import StacksCheckRecall

/-!
# Fibre products and equalizers along 1-morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` preserves
fibre products. If it is faithful, it also preserves equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/- Lemma 96.17.3 (1): a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf` transforms fibre products into fibre products, i.e.
`toFunctor f` preserves limits of shape `WalkingCospan`. -/
@[stacks 06WZ] #check
  (CategoryTheory.BasedFunctor.preservesPullbacksInGroupoids (toBasedFunctor f) :
    PreservesLimitsOfShape WalkingCospan (toFunctor f))

variable [Functor.Faithful (toFunctor f)]

/- Lemma 96.17.3 (2): if a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful, then `f` transforms equalizers into
equalizers, i.e. `toFunctor f` preserves limits of shape `WalkingParallelPair`. -/
@[stacks 06WZ] #check
  (CategoryTheory.BasedFunctor.preservesEqualizersInGroupoids (toBasedFunctor f) :
    PreservesLimitsOfShape WalkingParallelPair (toFunctor f))

end AlgebraicGeometry.GroupoidsOver
