module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback

/-!
# Flat pullback on Chow groups

This file defines flat pullback on Chow groups over a universally catenary dimensioned base
and records its value on cycle representatives.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalEquivalence

/-- Flat pullback sends rational boundaries in degree `k` to rational boundaries in degree
`k + r`. -/
theorem flatPullback_mem_boundaries
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    @boundaries Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k ≤
      (@boundaries X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))).comap
        (CycleGroup.flatPullback δ X Y f r k) := sorry

end RationalEquivalence

namespace ChowGroup

/-- Flat pullback on Chow groups over a universally catenary dimensioned base. -/
noncomputable def flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ)) :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance k)
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ)))
    (CycleGroup.flatPullback δ X Y f r k)
    (RationalEquivalence.flatPullback_mem_boundaries δ X Y f r k)

/-- Flat pullback on Chow groups is computed on cycle representatives by cycle flat pullback
followed by passage to the Chow class. -/
theorem flatPullback_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    flatPullback δ X Y f r k
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))
        (CycleGroup.flatPullback δ X Y f r k α) := sorry

end ChowGroup

end AlgebraicGeometry
