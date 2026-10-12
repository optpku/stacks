/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.FixedRank
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 42.38.7: Intersecting with the `i`th Chern class of every pullback of a
rank-`r` finite locally free module defines a degree-`i` bivariant Chow class. -/
@[stacks 0B7H] #check (AlgebraicGeometry.ChernClass.FixedRank.component :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)),
    ChowCohomology.degree δ p (i : ℤ))
