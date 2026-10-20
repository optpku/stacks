/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Displayed

/-!
# Total category of unbounded right-derived realizations

This leaf gives a stable name to the total category of the displayed realization family and
exposes its projection to the source filtered complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The total category of filtered complexes equipped with unbounded right-derived
spectral-sequence realizations. -/
@[stacks 0BKK "total category of unbounded right-derived realizations"]
abbrev Total
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :=
  DisplayedCategory.Total (SpectralSequence.displayedCategory F)

namespace Total

/-- Forget a total unbounded right-derived realization to its source filtered complex. -/
@[stacks 0BKK "base of a total unbounded right-derived realization"]
abbrev forgetBase
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    Realization.Total F ⥤ FilteredComplex A :=
  DisplayedCategory.Total.forget (SpectralSequence.displayedCategory F)

/-- The base of a total unbounded right-derived realization is its stored filtered complex. -/
@[simp, stacks 0BKK "base of a total unbounded right-derived realization"]
theorem forgetBase_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    (S : Realization.Total F) :
    (forgetBase F).obj S = S.base := sorry

/-- The base map of a total unbounded right-derived realization morphism is its stored map. -/
@[simp, stacks 0BKK "base map of a total unbounded right-derived realization"]
theorem forgetBase_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Realization.Total F} (m : S ⟶ T) :
    (forgetBase F).map m = m.base := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
