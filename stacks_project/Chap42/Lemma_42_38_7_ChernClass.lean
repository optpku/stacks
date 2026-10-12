/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.FixedRank

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Intersection with the `i`th Chern class of a finite locally free module on
relative Chow groups. -/
noncomputable abbrev chernClassCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℕ)) :=
  ChernClass.FixedRank.chernClassCap δ p E r i k

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.ChernClass

/-- The degree-`i` operational Chern class of a finite locally free module of rank `r`. -/
noncomputable abbrev component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    ChowCohomology.degree δ p (i : ℤ) :=
  FixedRank.component δ p E r i

end AlgebraicGeometry.ChernClass
