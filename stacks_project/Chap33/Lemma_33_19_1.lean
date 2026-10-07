module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.GenericPoints

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.19.1: let `f : X ⟶ Y` be locally of finite type, let `x : X`, and assume that
`𝒪_{Y, f x}` is Noetherian of dimension at most `1`. If `d : ℕ` is such that for every generic
point `η` of an irreducible component of `X` containing `x`, the fiber dimension at `η` satisfies
`f.fiberDimensionAt η = d`, then `f.fiberDimensionAt x = d`. This formalizes the source quantity
`dim_x(X_y)` by the canonical owner `Scheme.Hom.fiberDimensionAt`, with `y = f x`. -/
@[stacks 0B2I] #check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_eq_of_eq_at_genericPoints_specializingTo :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (d : ℕ),
      IsNoetherianRing (Y.presheaf.stalk (f x)) →
      ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1 →
      (∀ η : X, η ∈ genericPoints X → Specializes η x →
        f.fiberDimensionAt η = d) →
      f.fiberDimensionAt x = d)
