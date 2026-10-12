/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood

@[expose] public section

open CategoryTheory

universe u

/- The canonical `n`th infinitesimal-neighbourhood scheme associated to an immersion. -/
#check (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.scheme :
  {Z X : AlgebraicGeometry.Scheme.{u}} → (i : Z ⟶ X) →
    [AlgebraicGeometry.IsImmersion i] → ℕ → AlgebraicGeometry.Scheme.{u})
