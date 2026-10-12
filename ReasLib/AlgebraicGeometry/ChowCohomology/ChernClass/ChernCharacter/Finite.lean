/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- On a quasi-compact scheme of dimension at most `d`, Chern-character components
above degree `d` vanish. -/
theorem character_eq_zero_of_dim_lt
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [CompactSpace X] (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree]
    (d i : ℕ) (hXdim : topologicalKrullDim X ≤ d) (hdi : d < i) :
    character δ p classes E i = 0 := sorry

/-- On a quasi-compact scheme of dimension at most `d`, every homogeneous projection
of `totalCharacter` agrees with the corresponding full Chern-character component. -/
theorem totalCharacter_component
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [CompactSpace X] (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree]
    (d i : ℕ) (hXdim : topologicalKrullDim X ≤ d) :
    ChowCohomology.Nonnegative.rationalComponent δ p i
        (totalCharacter δ p classes E d) = character δ p classes E i := sorry

end AlgebraicGeometry.ChernClass.Theory
