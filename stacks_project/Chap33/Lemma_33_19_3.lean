/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.GenericPoints

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.19.3: let `f : X ⟶ Y` be locally of finite type, let `x : X`, and assume that
`𝒪_{Y, f x}` is Noetherian. Let `d : ℕ` be such that for every generic point `η` of an
irreducible component of `X` containing `x`, we have `f η ≠ f x` and `f.fiberDimensionAt η = d`.
Then
`f.fiberDimensionAt x ≤
  (((d + (ringKrullDim (Y.presheaf.stalk (f x))).unbotD 0 - 1 : ℕ∞) : WithBot ℕ∞))`.
This states the source arithmetic bound `dim_x(X_y) ≤ d + dim(𝒪_{Y, f x}) - 1` directly on the
canonical owner `Scheme.Hom.fiberDimensionAt`, with `y = f x`, in the ambient `WithBot ℕ∞`
dimension codomain. -/
@[stacks 0B2K] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.at_le_generic_add_ringKrullDim_sub_one :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (d : ℕ),
      IsNoetherianRing (Y.presheaf.stalk (f x)) →
      (∀ η : X, η ∈ genericPoints X → Specializes η x → f η ≠ f x) →
      (∀ η : X, η ∈ genericPoints X → Specializes η x →
        f.fiberDimensionAt η = d) →
      f.fiberDimensionAt x ≤
        (((d + (ringKrullDim (Y.presheaf.stalk (f x))).unbotD 0 - 1 : ℕ∞) : WithBot ℕ∞)))
