/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension.Inclusion
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0.Equivalence

/-!
# Grothendieck groups of intervals in the coherent support filtration

This file defines the Serre quotient of coherent sheaves supported in dimension at most an
upper bound by those supported in dimension at most a lower bound. It also constructs the
canonical maps from cycles and from the associated graded Grothendieck group.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Inside coherent sheaves supported in dimension at most `upper`, the objects supported in
dimension at most `lower`. -/
def filteredLowerCoh {X : Scheme.{u}} (d : X → ℤ) (upper lower : ℤ) :
    ObjectProperty (RingedSpace.CohLE X.toRingedSpace d upper) :=
  (RingedSpace.Coh.supportDimensionLE d lower).inverseImage
    (RingedSpace.Coh.supportDimensionLE d upper).ι

/-- Membership in `filteredLowerCoh d upper lower` is the pointwise support bound by `lower`. -/
theorem filteredLowerCoh_iff {X : Scheme.{u}} (d : X → ℤ) (upper lower : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace d upper) :
    filteredLowerCoh d upper lower F ↔
      ∀ x ∈ RingedSpace.moduleSupport F.obj.obj, d x ≤ lower := sorry

/-- The lower part of a bounded coherent support filtration is a Serre class in the upper
part. -/
instance filteredLowerCohIsSerreClass
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (upper lower : ℤ) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (filteredLowerCoh (f.relativeDimensionFunction δ) upper lower).IsSerreClass := sorry

/-- The Serre quotient `Coh≤upper(X) / Coh≤lower(X)` for the relative dimension function. -/
abbrev FilteredCoh
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (upper lower : ℤ) :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (filteredLowerCoh (f.relativeDimensionFunction δ) upper lower).isoModSerre.Localization

namespace FilteredCoh

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (upper lower : ℤ)

/-- The quotient image of an object of `Coh≤upper(X)`. -/
noncomputable def quotientObj
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper) :
    FilteredCoh f δ upper lower :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (filteredLowerCoh (f.relativeDimensionFunction δ) upper lower).isoModSerre.Q.obj F

/-- `quotientObj` is the object map of the canonical Serre quotient. -/
theorem quotientObj_eq
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    quotientObj f δ upper lower F =
      (filteredLowerCoh (f.relativeDimensionFunction δ) upper lower).isoModSerre.Q.obj F := sorry

end FilteredCoh

/-- The Grothendieck group of `Coh≤upper(X) / Coh≤lower(X)`. -/
abbrev FilteredK0
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (upper lower : ℤ) :=
  AbelianK0 (FilteredCoh f δ upper lower)

namespace FilteredK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (upper lower : ℤ)

/-- The Grothendieck class of a coherent object after passage to the filtered Serre quotient. -/
noncomputable def of
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper) :
    FilteredK0 f δ upper lower :=
  AbelianK0.of (FilteredCoh.quotientObj f δ upper lower F)

/-- `of` is the class of the canonical quotient object. -/
theorem of_def
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper) :
    of f δ upper lower F =
      AbelianK0.of (FilteredCoh.quotientObj f δ upper lower F) := sorry

end FilteredK0

namespace CycleGroup

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The value in `K₀(Coh≤k+1(X) / Coh≤k-1(X))` attached to a degree-`k` cycle. -/
noncomputable def toFilteredK0Value
    (α : AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k) :
    FilteredK0 f δ (k + 1) (k - 1) :=
  FilteredK0.of f δ (k + 1) (k - 1)
      ((RingedSpace.CohLE.inclusion (le_add_of_nonneg_right zero_le_one)).obj
        (GradedK0.positiveObject f δ k α)) -
    FilteredK0.of f δ (k + 1) (k - 1)
      ((RingedSpace.CohLE.inclusion (le_add_of_nonneg_right zero_le_one)).obj
        (GradedK0.negativeObject f δ k α))

/-- The filtered cycle value sends zero to zero. -/
theorem toFilteredK0Value_zero : toFilteredK0Value f δ k 0 = 0 := sorry

/-- The filtered cycle value preserves addition. -/
theorem toFilteredK0Value_add
    (α β : AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k) :
    toFilteredK0Value f δ k (α + β) =
      toFilteredK0Value f δ k α + toFilteredK0Value f δ k β := sorry

/-- The additive map from degree-`k` cycles to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))`. -/
noncomputable def toFilteredK0 :
    AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k →+
      FilteredK0 f δ (k + 1) (k - 1) where
  toFun := toFilteredK0Value f δ k
  map_zero' := toFilteredK0Value_zero f δ k
  map_add' := toFilteredK0Value_add f δ k

/-- The cycle map is the difference of the widened positive and negative quotient classes. -/
theorem toFilteredK0_apply
    (α : AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k) :
    toFilteredK0 f δ k α =
      FilteredK0.of f δ (k + 1) (k - 1)
          ((RingedSpace.CohLE.inclusion (le_add_of_nonneg_right zero_le_one)).obj
            (GradedK0.positiveObject f δ k α)) -
        FilteredK0.of f δ (k + 1) (k - 1)
          ((RingedSpace.CohLE.inclusion (le_add_of_nonneg_right zero_le_one)).obj
            (GradedK0.negativeObject f δ k α)) := sorry

end CycleGroup

namespace GradedK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The canonical transition from the degree-`k` graded Grothendieck group to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))`. -/
noncomputable def toFilteredK0 :
    GradedK0 f δ k →+ FilteredK0 f δ (k + 1) (k - 1) :=
  (CycleGroup.toFilteredK0 f δ k).comp (toCycle f δ k)

/-- The filtered transition composed with the cycle-to-graded map is the explicit filtered
cycle map. -/
theorem toFilteredK0_comp_toK0 :
    (toFilteredK0 f δ k).comp (toK0 f δ k) = CycleGroup.toFilteredK0 f δ k := sorry

/-- The filtered transition sends an object class to the class of the same coherent sheaf
viewed one step higher in the support filtration. -/
theorem toFilteredK0_of
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    toFilteredK0 f δ k (of f δ k F) =
      FilteredK0.of f δ (k + 1) (k - 1)
        ((RingedSpace.CohLE.inclusion (le_add_of_nonneg_right zero_le_one)).obj F) := sorry

end GradedK0

end AlgebraicGeometry.Scheme.Modules
