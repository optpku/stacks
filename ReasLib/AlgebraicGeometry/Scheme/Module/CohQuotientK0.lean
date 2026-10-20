/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FilteredK0
public import ReasLib.CategoryTheory.Functor.Exactness.Composition

/-!
# Grothendieck groups of coherent Serre quotients

This file constructs the full coherent quotient by a support bound and the canonical transition
from the corresponding bounded coherent quotient.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The Serre quotient `Coh(X) / Coh≤lower(X)` for the relative dimension function. -/
abbrev CohQuotient
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (lower : ℤ) :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (RingedSpace.Coh.supportDimensionLE
    (f.relativeDimensionFunction δ) lower).isoModSerre.Localization

namespace CohQuotient

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The quotient image of a coherent sheaf in `Coh(X) / Coh≤lower(X)`. -/
noncomputable def quotientObj (lower : ℤ) (F : RingedSpace.Coh X.toRingedSpace) :
    CohQuotient f δ lower :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (RingedSpace.Coh.supportDimensionLE
    (f.relativeDimensionFunction δ) lower).isoModSerre.Q.obj F

/-- `quotientObj` is the object map of the canonical Serre quotient. -/
theorem quotientObj_eq (lower : ℤ) (F : RingedSpace.Coh X.toRingedSpace) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    quotientObj f δ lower F =
      (RingedSpace.Coh.supportDimensionLE
        (f.relativeDimensionFunction δ) lower).isoModSerre.Q.obj F := sorry

end CohQuotient

/-- The Grothendieck group of `Coh(X) / Coh≤lower(X)`. -/
abbrev CohQuotientK0
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (lower : ℤ) :=
  AbelianK0 (CohQuotient f δ lower)

namespace CohQuotientK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The Grothendieck class of a coherent sheaf in the full coherent quotient. -/
noncomputable def of (lower : ℤ) (F : RingedSpace.Coh X.toRingedSpace) :
    CohQuotientK0 f δ lower :=
  AbelianK0.of (CohQuotient.quotientObj f δ lower F)

/-- `of` is the class of the canonical quotient object. -/
theorem of_def (lower : ℤ) (F : RingedSpace.Coh X.toRingedSpace) :
    of f δ lower F = AbelianK0.of (CohQuotient.quotientObj f δ lower F) := sorry

end CohQuotientK0

namespace CohQuotient

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The exact functor from bounded coherent sheaves to the full coherent quotient. -/
noncomputable def fromBounded (upper lower : ℤ) :
    RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper ⥤ₑ
      CohQuotient f δ lower :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ExactFunctor.comp
    (ObjectProperty.SerreClassLocalization.inclusionExactFunctor
      (RingedSpace.Coh.supportDimensionLE (f.relativeDimensionFunction δ) upper))
    (ObjectProperty.SerreClassLocalization.quotientExactFunctor
      (RingedSpace.Coh.supportDimensionLE (f.relativeDimensionFunction δ) lower))

/-- The lower support subcategory lies in the kernel of `fromBounded`. -/
theorem lower_le_kernel (upper lower : ℤ) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    filteredLowerCoh (f.relativeDimensionFunction δ) upper lower ≤
      (fromBounded f δ upper lower).obj.kernel := sorry

end CohQuotient

namespace FilteredCoh

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The exact transition from the bounded coherent quotient to the full coherent quotient. -/
noncomputable def toCohQuotient (upper lower : ℤ) :
    FilteredCoh f δ upper lower ⥤ₑ CohQuotient f δ lower :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ObjectProperty.SerreClassLocalization.inducedExactFunctor
    (filteredLowerCoh (f.relativeDimensionFunction δ) upper lower)
    (CohQuotient.fromBounded f δ upper lower)
    (CohQuotient.lower_le_kernel f δ upper lower)

end FilteredCoh

namespace FilteredK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The homomorphism on `K₀` induced by the bounded-to-full quotient transition. -/
noncomputable def toCohQuotient (upper lower : ℤ) :
    FilteredK0 f δ upper lower →+ CohQuotientK0 f δ lower :=
  AbelianK0.map (FilteredCoh.toCohQuotient f δ upper lower)

/-- The transition sends a bounded quotient class to the class of its underlying coherent
sheaf in the full quotient. -/
theorem toCohQuotient_of (upper lower : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) upper) :
    toCohQuotient f δ upper lower (of f δ upper lower F) =
      CohQuotientK0.of f δ lower F.obj := sorry

end FilteredK0

end AlgebraicGeometry.Scheme.Modules
