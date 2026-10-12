/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.Topology.KrullDimension.Local

/-!
# Étale Krull dimension of algebraic spaces

The étale Krull dimension is the supremum of local dimensions of étale scheme charts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale Krull dimension of an algebraic space is the supremum of the local
topological Krull dimensions at points of all its étale scheme charts. -/
noncomputable def etaleKrullDim {S : Scheme.{u}} (X : AlgebraicSpace S) : WithBot ℕ∞ :=
  ⨆ (T : Over S) (f : ofOver T ⟶ X)
    (_ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) (t : T.left),
    topologicalKrullDimAt t

/-- The étale Krull dimension of a scheme viewed as an algebraic space equals
its topological Krull dimension. -/
theorem etaleKrullDim_ofOver {S : Scheme.{u}} (T : Over S) :
    etaleKrullDim (ofOver T) = topologicalKrullDim T.left := sorry

end AlgebraicGeometry.AlgebraicSpace
