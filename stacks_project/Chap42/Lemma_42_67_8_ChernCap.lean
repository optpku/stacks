module

public import stacks_project.Chap42.Lemma_42_38_7_ChernClass

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/-- Intersection with the `i`th Chern class, extended by zero when `i` is larger
than the rank of the finite locally free module. -/
noncomputable def componentMap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℤ)) :=
  if hi : i < r + 1 then chernClassCap δ p E r ⟨i, hi⟩ k else 0

/-- In its rank-bounded range, `componentMap` is the canonical Chern-class cap. -/
theorem componentMap_eq_chernClassCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (hi : i < r + 1) :
    componentMap δ p E r i k = chernClassCap δ p E r ⟨i, hi⟩ k := sorry

/-- Above the rank of the module, `componentMap` is the zero additive homomorphism. -/
theorem componentMap_eq_zero_of_rank_lt
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (hi : r < i) :
    componentMap δ p E r i k = 0 := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap
