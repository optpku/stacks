module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Definition 87.37.3: Let `S` be a scheme and `X` a formal algebraic space over `S`.
Explicit `ReductionData X` represents the reduction `X_red`. For a closed subset `T`
of its points, `Recompletion.functor R T` is the completion of `X` along `T`. -/
@[stacks 0GVS] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.functor :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X),
      TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points R.space) →
        (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.functor_obj :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X)
    (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points R.space))
    (U : (Over S)ᵒᵖ),
    (Recompletion.functor R T).obj U =
      {x : X.obj U // Recompletion.mapsInto R
        (T : Set (AlgebraicGeometry.AlgebraicSpace.Points R.space)) x})

#check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.ι :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X)
    (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points R.space)),
    Recompletion.functor R T ⟶ X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isFormalAlgebraicSpace :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X)
    (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points R.space)),
    IsFormalAlgebraicSpace (Recompletion.functor R T))
