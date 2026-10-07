module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

/-!
# Abutments of total truncation-filtration realizations

This leaf exposes the degreewise abutment of a truncation-filtration realization.  Its target is
cohomology of the total right-derived functor on the derived base object, so downstream arguments
do not need to unfold the representative preimage used by the filtration.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Degree-`n` homology of the filtered model of a total truncation realization. -/
@[stacks 0BKM "abutment source functor on total truncation realizations"]
noncomputable abbrev abutmentSource (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetUnderlying F ⋙ HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Degree-`n` cohomology of the total right-derived value on the derived base object. -/
@[stacks 0BKM "abutment target functor on total truncation realizations"]
noncomputable abbrev abutmentTarget (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ Functor.RightDerived.Homotopy.cohomologyFunctor F n

/-- Naturality of the stored abutment comparisons on total truncation realizations. -/
@[reassoc, stacks 0BKM "naturality of the total truncation abutment comparison"]
theorem abutmentComparison_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (T.obj.targetIso n).hom =
      (S.obj.targetIso n).hom ≫ (abutmentTarget F n).map m := sorry

/-- The degree-`n` abutment comparison, natural in total truncation realization maps. -/
@[stacks 0BKM "total truncation abutment comparison"]
noncomputable def abutmentComparison (n : ℤ) :
    abutmentSource F n ≅ abutmentTarget F n :=
  NatIso.ofComponents (fun S => S.obj.targetIso n)
    (fun m => abutmentComparison_naturality F n m)

/-- The abutment source evaluates to homology of the stored filtered model. -/
@[simp, stacks 0BKM "abutment source object on total truncation realizations"]
theorem abutmentSource_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentSource F n).obj S = S.obj.filtered.underlying.homology n := sorry

/-- The abutment source maps by homology of the filtered realization map. -/
@[simp, stacks 0BKM "abutment source map on total truncation realizations"]
theorem abutmentSource_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.displayed.filteredMap) n := sorry

/-- The abutment target evaluates to total right-derived cohomology of the derived base. -/
@[simp, stacks 0BKM "abutment target object on total truncation realizations"]
theorem abutmentTarget_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentTarget F n).obj S =
      (Functor.RightDerived.Homotopy.cohomologyFunctor F n).obj S.base := sorry

/-- The abutment target maps by the derived-category cohomology functor. -/
@[simp, stacks 0BKM "abutment target map on total truncation realizations"]
theorem abutmentTarget_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m =
      (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map m.base := sorry

/-- A component of the total truncation abutment comparison is the stored target isomorphism. -/
@[simp, stacks 0BKM "component of the total truncation abutment comparison"]
theorem abutmentComparison_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).app S = S.obj.targetIso n := sorry

/-- The forward component of the total truncation abutment comparison. -/
@[simp, stacks 0BKM "forward component of the total truncation abutment comparison"]
theorem abutmentComparison_hom_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).hom.app S = (S.obj.targetIso n).hom := sorry

/-- The inverse component of the total truncation abutment comparison. -/
@[simp, stacks 0BKM "inverse component of the total truncation abutment comparison"]
theorem abutmentComparison_inv_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).inv.app S = (S.obj.targetIso n).inv := sorry

/-- Naturality of the forward total truncation abutment comparison. -/
@[reassoc, stacks 0BKM "forward naturality of the total truncation abutment comparison"]
theorem abutmentComparison_hom_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (abutmentComparison F n).hom.app T =
      (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m := sorry

/-- Naturality of the inverse total truncation abutment comparison. -/
@[reassoc, stacks 0BKM "inverse naturality of the total truncation abutment comparison"]
theorem abutmentComparison_inv_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m ≫ (abutmentComparison F n).inv.app T =
      (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m := sorry

/-- Conjugating a target abutment map by the comparison recovers the source map. -/
@[reassoc, stacks 0BKM "source-map computation for the total truncation abutment"]
theorem abutmentComparison_source_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m ≫
        (abutmentComparison F n).inv.app T =
      (abutmentSource F n).map m := sorry

/-- Conjugating a source abutment map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 0BKM "target-map computation for the total truncation abutment"]
theorem abutmentComparison_target_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m ≫
        (abutmentComparison F n).hom.app T =
      (abutmentTarget F n).map m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
