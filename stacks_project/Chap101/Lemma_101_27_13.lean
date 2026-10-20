module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.CoveringLift
import StacksCheckRecall

/-!
# Fppf covering lifts for morphisms of algebraic stacks

A morphism of algebraic stacks which is surjective, flat, and locally of finite
presentation has the fppf lifting property for objects of the target over a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.27.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
surjective, flat, and locally of finite presentation. Then for every scheme `U`
and object `y` of `Y` over `U` there exists an fppf covering `{U_i ⟶ U}` and
objects `x_i` of `X` over `U_i` such that `f(x_i) ≅ y|_{U_i}` in `Y_{U_i}`. -/
@[stacks 06QA] #check (AlgebraicGeometry.AlgebraicStack.exists_fppfCovering_iso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.Surjective f]
    [AlgebraicGeometry.AlgebraicStack.Flat f]
    [AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y),
    Groupoids.Hom.existsCoveringLift StandardTopology.fppf f y)
