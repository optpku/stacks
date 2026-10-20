/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abutments of total unbounded right-derived realizations

This leaf gives the construction-neutral source and target functors for the degreewise abutment
of a total realization.  The comparison is assembled from the `targetIso` field already owned by
the generic realization; no new representative or resolution choice is introduced here.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Total

/-- Degree-`n` homology of the filtered model of a total realization. -/
@[stacks 0BKK "abutment source functor on total right-derived realizations"]
noncomputable abbrev abutmentSource (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetUnderlying F ⋙ HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Degree-`n` cohomology of the total right-derived value of the source filtered complex. -/
@[stacks 0BKK "abutment target functor on total right-derived realizations"]
noncomputable abbrev abutmentTarget (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ FilteredComplex.underlyingFunctor ⋙
    Functor.RightDerived.Homotopy.cochainCohomologyFunctor F n

/-- Naturality of the stored generic abutment comparisons on the total realization category. -/
@[reassoc, stacks 0BKK "naturality of the total right-derived abutment comparison"]
theorem abutmentComparison_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (T.obj.targetIso n).hom =
      (S.obj.targetIso n).hom ≫ (abutmentTarget F n).map m := sorry

/-- The degree-`n` abutment comparison, natural in total realization maps. -/
@[stacks 0BKK "total right-derived abutment comparison"]
noncomputable def abutmentComparison (n : ℤ) :
    abutmentSource F n ≅ abutmentTarget F n :=
  NatIso.ofComponents (fun S => S.obj.targetIso n)
    (fun m => abutmentComparison_naturality F n m)

/-- The abutment source evaluates to homology of the stored filtered model. -/
@[simp, stacks 0BKK "abutment source object of a total right-derived realization"]
theorem abutmentSource_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentSource F n).obj S = S.obj.filtered.underlying.homology n := sorry

/-- The abutment source maps by homology of the filtered realization map. -/
@[simp, stacks 0BKK "abutment source map of a total right-derived realization"]
theorem abutmentSource_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.displayed.filteredMap) n := sorry

/-- The abutment target evaluates to total right-derived cohomology of the source complex. -/
@[simp, stacks 0BKK "abutment target object of a total right-derived realization"]
theorem abutmentTarget_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentTarget F n).obj S =
      Functor.RightDerived.Homotopy.cochainCohomology F S.base.underlying n := sorry

/-- The abutment target maps by the total right-derived cohomology functor. -/
@[simp, stacks 0BKK "abutment target map of a total right-derived realization"]
theorem abutmentTarget_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m =
      Functor.RightDerived.Homotopy.cochainCohomologyMap F
        (FilteredComplex.underlyingMap m.base) n := sorry

/-- A component of the total abutment comparison is the stored target isomorphism. -/
@[simp, stacks 0BKK "component of the total right-derived abutment comparison"]
theorem abutmentComparison_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).app S = S.obj.targetIso n := sorry

/-- The forward component of the total abutment comparison. -/
@[simp, stacks 0BKK "forward component of the total right-derived abutment comparison"]
theorem abutmentComparison_hom_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).hom.app S = (S.obj.targetIso n).hom := sorry

/-- The inverse component of the total abutment comparison. -/
@[simp, stacks 0BKK "inverse component of the total right-derived abutment comparison"]
theorem abutmentComparison_inv_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).inv.app S = (S.obj.targetIso n).inv := sorry

/-- Naturality of the forward total abutment comparison. -/
@[reassoc, stacks 0BKK "forward naturality of the total right-derived abutment comparison"]
theorem abutmentComparison_hom_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (abutmentComparison F n).hom.app T =
      (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m := sorry

/-- Naturality of the inverse total abutment comparison. -/
@[reassoc, stacks 0BKK "inverse naturality of the total right-derived abutment comparison"]
theorem abutmentComparison_inv_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m ≫ (abutmentComparison F n).inv.app T =
      (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m := sorry

/-- Conjugating a target abutment map by the comparison recovers the source map. -/
@[reassoc, stacks 0BKK "source-map computation for the total right-derived abutment"]
theorem abutmentComparison_source_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m ≫
        (abutmentComparison F n).inv.app T =
      (abutmentSource F n).map m := sorry

/-- Conjugating a source abutment map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 0BKK "target-map computation for the total right-derived abutment"]
theorem abutmentComparison_target_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m ≫
        (abutmentComparison F n).hom.app T =
      (abutmentTarget F n).map m := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
