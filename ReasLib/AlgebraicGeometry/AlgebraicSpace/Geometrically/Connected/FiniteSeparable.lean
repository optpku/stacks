module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically

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

/-- An algebraic space over a field is geometrically connected if and only if its
base change along `FieldExtension.specMap k K` has connected space of points for
every finite separable field extension `K/k`. -/
@[stacks 0A17]
theorem iff_finiteSeparable {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace (Points (baseChange (FieldExtension.specMap k K) X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
