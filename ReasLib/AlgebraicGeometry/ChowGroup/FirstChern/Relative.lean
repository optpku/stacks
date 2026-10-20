module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalEquivalence

/-- Rational-equivalence boundaries lie in the kernel of the reindexed first-Chern cap
map on cycles. -/
theorem firstChernClassCap_mem_ker
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ) :
    @boundaries X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k ≤
      ((Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)).comp
        (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm)).ker := sorry

end RationalEquivalence

namespace ChowGroup

/-- Intersection with the first Chern class of an invertible module on relative Chow
groups. -/
noncomputable def firstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ) :
    RelativeChow δ X k →+ RelativeChow δ X (k - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance k)
    ((Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)).comp
      (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
        (sub_add_cancel k 1).symm))
    (RationalEquivalence.firstChernClassCap_mem_ker δ X ℒ k)

/-- The Chow-level first-Chern cap map is computed on a representative by the reindexed
cycle-level first-Chern operation. -/
theorem firstChernClassCap_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    firstChernClassCap δ X ℒ k
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k α) =
      Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)
        (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm α) := sorry

end ChowGroup

end AlgebraicGeometry
