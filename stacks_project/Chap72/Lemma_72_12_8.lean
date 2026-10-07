module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap72.Lemma_72_14_3_Geometrically

/-!
# Finite-separable test for geometric connectedness of algebraic spaces

An algebraic space over a field `k` is geometrically connected if and only if its
base change to every finite separable field extension of `k` is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/-- Lemma 72.12.8: Let `k` be a field. Let `X` be an algebraic space over `k`.
Then `X` is geometrically connected if and only if for every finite separable
field extension `K/k`, the algebraic space obtained by base change of `X` along
`FieldExtension.specMap k K` is connected. -/
@[stacks 0A17]
theorem iff_finiteSeparable {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace (Points (baseChange (FieldExtension.specMap k K) X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
