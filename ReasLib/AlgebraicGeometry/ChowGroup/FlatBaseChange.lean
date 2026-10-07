module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.FlatBaseChange

/-!
# Flat base change of Chow groups

This file defines dimension-shifted flat base change on Chow groups, records
its value on cycle representatives, and proves compatibility with flat pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalEquivalence

/-- Dimension-shifted flat base change sends rational boundaries to rational boundaries. -/
theorem baseChangePullback_mem_boundaries
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    @boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k ≤
      (@boundaries (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)).comap
        (CycleGroup.baseChangePullback g δ δ' c hcompat f k) := sorry

end RationalEquivalence

namespace ChowGroup

/-- Flat base change compatible with `δ` and `δ'` up to `c` defines an additive
pullback from degree `k` Chow groups to degree `k + c` Chow groups. -/
noncomputable def baseChangePullback
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c) :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries X
      (LocallyOfFiniteType.isLocallyNoetherian f)
      (f.relativeDimensionFunction δ) inferInstance k)
    (@RationalEquivalence.boundaries (pullback f g)
      (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
      ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c))
    (CycleGroup.baseChangePullback g δ δ' c hcompat f k)
    (RationalEquivalence.baseChangePullback_mem_boundaries
      g δ δ' c hcompat f k)

/-- Base change on Chow groups is computed on representatives by base change on cycles. -/
theorem baseChangePullback_chowClass
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    baseChangePullback g δ δ' c hcompat f k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat f k α) := sorry

/-- Dimension-shifted base change commutes with flat pullback on Chow groups. -/
theorem baseChangePullback_flatPullback
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    (@reindex ((Over.pullback g).obj Y).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj Y).hom
          (LocallyOfFiniteType.instOverPullbackObj g Y) inferInstance)
        (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ') inferInstance
        ((k + (r : ℤ)) + c) ((k + c) + (r : ℤ))
        (by
          rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
            ← add_assoc k c (r : ℤ)])).toAddMonoidHom.comp
          ((baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
            (flatPullback δ Y X f r k)) =
      (flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
          ((Over.pullback g).map f) r (k + c)).comp
        (baseChangePullback g δ δ' c hcompat X.hom k) := sorry

end ChowGroup

end AlgebraicGeometry
