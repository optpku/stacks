module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverField.DimensionZero
import StacksCheckRecall

/-!
# Conditions on an algebraic space locally of finite type over a field

For an algebraic space locally of finite type over a field, discreteness of the
space of points, vanishing of its topological Krull dimension, vanishing of the
étale-local dimension, and local quasi-finiteness of the structure morphism are
equivalent. If the algebraic space is decent, finiteness of the space of points
implies these conditions.

The source's zero-dimensional conditions are expressed as dimension at most
zero in `WithBot ℕ∞`. For nonempty spaces this means equality with zero, and it
also includes the empty space, whose dimensions are `⊥`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.18.8: For an algebraic space locally of finite type over a field,
conditions (2), (3), (4), and (5) are equivalent. -/
@[stacks 0ACA] #check
  (AlgebraicGeometry.AlgebraicSpace.tfae_discrete_dimension_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f],
    List.TFAE
      [ DiscreteTopology (Points X)
      , topologicalKrullDim (Points X) ≤ 0
      , dimension X ≤ 0
      , LocallyQuasiFinite f ])

/- Lemma 68.18.8: If the algebraic space is decent, condition (1) implies
local quasi-finiteness and hence all four equivalent conditions. -/
@[stacks 0ACA] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_isDecent_finite :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
      [IsDecent X] [Finite (Points X)], LocallyQuasiFinite f)

end AlgebraicGeometry.AlgebraicSpace
