/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.MaximalIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.5.3: with `Y = X ×_{Spec(k)} Spec(K)` and `x = (pullback.fst f ι) y`, if
`dim(𝒪_{X, x}) = dim(𝒪_{Y, y})` and `κ(x) ⊗[k] K` is reduced, then
`𝔪_x 𝒪_{Y, y} = 𝔪_y`. The reducedness hypothesis holds, for example, when `κ(x)/k` or `K/k`
is separable. -/
@[stacks 0C50] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.toSourceMap_mapsMaximalIdeal_of_ringKrullDim_eq_of_isReduced :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (y : FieldExtension.baseChange k K f),
      ringKrullDim (X.presheaf.stalk (FieldExtension.toSource k K f y)) =
          ringKrullDim ((FieldExtension.baseChange k K f).presheaf.stalk y) →
        _root_.IsReduced (FieldExtension.Stalk.pointTensor k K f y) →
          Ideal.map (FieldExtension.Stalk.toSourceMap k K f y).hom
              (IsLocalRing.maximalIdeal
                (X.presheaf.stalk (FieldExtension.toSource k K f y))) =
            IsLocalRing.maximalIdeal ((FieldExtension.baseChange k K f).presheaf.stalk y))
