module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Integral
import StacksCheckRecall

/-!
# Definition 72.14.1

An algebraic space over a field `k` is geometrically integral over `k` if every
field base change is integral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.14.1: an algebraic space `X` over a field `k` is geometrically integral
over `k` if the algebraic space `X_K` is integral for every field extension `K` of `k`. -/
@[stacks 0DMW] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral.iff_isIntegral_baseChange :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
      GeometricallyIntegral X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (baseChange (Spec.map (ofHom (algebraMap k K))) X))
