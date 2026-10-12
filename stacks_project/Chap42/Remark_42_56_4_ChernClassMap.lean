/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernClass

@[expose] public section

open CategoryTheory

universe u

/- The vector-bundle `K₀` total Chern-class map is available from its reusable
mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p],
      AlgebraicGeometry.ChernClass.Theory δ p →
        AlgebraicGeometry.Scheme.VectorBundleK0 X →
          AlgebraicGeometry.ChowCohomology.Nonnegative.Completion δ p)
