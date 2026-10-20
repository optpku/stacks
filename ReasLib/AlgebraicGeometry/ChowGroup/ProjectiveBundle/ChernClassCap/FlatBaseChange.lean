module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.FixedRank

/-!
# Chern-class caps and flat base change

This file records the graded Chern-class cap maps and their compatibility with
dimension-shifted flat base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

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
  if hi : i < r + 1 then
    AlgebraicGeometry.ChernClass.FixedRank.chernClassCap δ p E r ⟨i, hi⟩ k
  else 0

/-- In its rank-bounded range, `componentMap` is the canonical Chern-class cap. -/
theorem componentMap_eq_chernClassCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (hi : i < r + 1) :
    componentMap δ p E r i k =
      AlgebraicGeometry.ChernClass.FixedRank.chernClassCap δ p E r ⟨i, hi⟩ k := sorry

/-- Above the rank of the module, `componentMap` is the zero additive homomorphism. -/
theorem componentMap_eq_zero_of_rank_lt
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (hi : r < i) :
    componentMap δ p E r i k = 0 := sorry

/-- Dimension-shifted flat base change commutes with capping by every Chern
class of a finite locally free module and its canonical pullback. -/
theorem baseChangePullback
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : ℕ) (k : ℤ) :
    (@ChowGroup.reindex ((Over.pullback g).obj X).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj X).hom
          (LocallyOfFiniteType.instOverPullbackObj g X) inferInstance)
        (((Over.pullback g).obj X).hom.relativeDimensionFunction δ') inferInstance
        ((k - (i : ℤ)) + c) (k + c - (i : ℤ))
        (sub_add_eq_add_sub k (i : ℤ) c)).toAddMonoidHom.comp
          ((AlgebraicGeometry.ChowGroup.baseChangePullback g δ δ' c hcompat X.hom
              (k - (i : ℤ))).comp
            (componentMap δ X.hom E r i k)) =
      (@componentMap S' ((Over.pullback g).obj X).left inferInstance δ' inferInstance
          ((Over.pullback g).obj X).hom (LocallyOfFiniteType.instOverPullbackObj g X)
          ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj E) r i
          (Scheme.Modules.pullback_isFiniteLocallyFreeOfRank
            (pullback.fst X.hom g) E r) (k + c)).comp
        (AlgebraicGeometry.ChowGroup.baseChangePullback g δ δ' c hcompat X.hom k) := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap
