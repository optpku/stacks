/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

/-!
# Abutments of total stupid-filtration realizations

This leaf specializes the neutral total abutment interface to the source cochain complex.  The
target is the ordinary cochain-level total right-derived cohomology functor, while the comparison
is exactly the `targetIso` stored by the stupid-filtration realization.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Degree-`n` homology of the filtered model of a total stupid realization. -/
@[stacks 0FLK "abutment source functor on total stupid realizations"]
noncomputable abbrev abutmentSource (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetUnderlying F ⋙ HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Degree-`n` total right-derived cohomology of the source cochain complex. -/
@[stacks 0FLK "abutment target functor on total stupid realizations"]
noncomputable abbrev abutmentTarget (n : ℤ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ Functor.RightDerived.Homotopy.cochainCohomologyFunctor F n

/-- Naturality of the stored abutment comparisons on total stupid realizations. -/
@[reassoc, stacks 0FLK "naturality of the total stupid abutment comparison"]
theorem abutmentComparison_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (T.obj.targetIso n).hom =
      (S.obj.targetIso n).hom ≫ (abutmentTarget F n).map m := sorry

/-- The degree-`n` abutment comparison, natural in total stupid realization maps. -/
@[stacks 0FLK "total stupid abutment comparison"]
noncomputable def abutmentComparison (n : ℤ) :
    abutmentSource F n ≅ abutmentTarget F n :=
  NatIso.ofComponents (fun S => S.obj.targetIso n)
    (fun m => abutmentComparison_naturality F n m)

/-- The abutment source evaluates to homology of the stored filtered model. -/
@[simp, stacks 0FLK "abutment source object on total stupid realizations"]
theorem abutmentSource_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentSource F n).obj S = S.obj.filtered.underlying.homology n := sorry

/-- The abutment source maps by homology of the filtered realization map. -/
@[simp, stacks 0FLK "abutment source map on total stupid realizations"]
theorem abutmentSource_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.displayed.filteredMap) n := sorry

/-- The abutment target evaluates to total right-derived cohomology of the source complex. -/
@[simp, stacks 0FLK "abutment target object on total stupid realizations"]
theorem abutmentTarget_obj (n : ℤ) (S : Realization.Total F) :
    (abutmentTarget F n).obj S =
      Functor.RightDerived.Homotopy.cochainCohomology F S.base n := sorry

/-- The abutment target maps by the cochain-level total right-derived functor. -/
@[simp, stacks 0FLK "abutment target map on total stupid realizations"]
theorem abutmentTarget_map (n : ℤ) {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m =
      Functor.RightDerived.Homotopy.cochainCohomologyMap F m.base n := sorry

/-- A component of the total stupid abutment comparison is the stored target isomorphism. -/
@[simp, stacks 0FLK "component of the total stupid abutment comparison"]
theorem abutmentComparison_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).app S = S.obj.targetIso n := sorry

/-- The forward component of the total stupid abutment comparison. -/
@[simp, stacks 0FLK "forward component of the total stupid abutment comparison"]
theorem abutmentComparison_hom_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).hom.app S = (S.obj.targetIso n).hom := sorry

/-- The inverse component of the total stupid abutment comparison. -/
@[simp, stacks 0FLK "inverse component of the total stupid abutment comparison"]
theorem abutmentComparison_inv_app (n : ℤ) (S : Realization.Total F) :
    (abutmentComparison F n).inv.app S = (S.obj.targetIso n).inv := sorry

/-- Naturality of the forward total stupid abutment comparison. -/
@[reassoc, stacks 0FLK "forward naturality of the total stupid abutment comparison"]
theorem abutmentComparison_hom_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentSource F n).map m ≫ (abutmentComparison F n).hom.app T =
      (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m := sorry

/-- Naturality of the inverse total stupid abutment comparison. -/
@[reassoc, stacks 0FLK "inverse naturality of the total stupid abutment comparison"]
theorem abutmentComparison_inv_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m ≫ (abutmentComparison F n).inv.app T =
      (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m := sorry

/-- Conjugating a target abutment map by the comparison recovers the source map. -/
@[reassoc, stacks 0FLK "source-map computation for the total stupid abutment"]
theorem abutmentComparison_source_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).hom.app S ≫ (abutmentTarget F n).map m ≫
        (abutmentComparison F n).inv.app T =
      (abutmentSource F n).map m := sorry

/-- Conjugating a source abutment map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 0FLK "target-map computation for the total stupid abutment"]
theorem abutmentComparison_target_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentComparison F n).inv.app S ≫ (abutmentSource F n).map m ≫
        (abutmentComparison F n).hom.app T =
      (abutmentTarget F n).map m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
