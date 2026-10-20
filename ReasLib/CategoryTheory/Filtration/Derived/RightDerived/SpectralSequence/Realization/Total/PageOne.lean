module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total.PageOne
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology

/-!
# First page of total unbounded right-derived realizations

This leaf promotes the first-page comparison of a generic right-derived realization to a natural
isomorphism on its total category.  The source reuses the neutral associated-spectral-sequence
page functor, while the target applies total right-derived cohomology to a graded piece of the
source filtered complex.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

/-- The `(p, q)` first-page entry, functorial on total right-derived realizations. -/
@[stacks 0BKK "first-page source functor on total right-derived realizations"]
noncomputable abbrev pageOneSource (p q : ℤ) :
    Realization.Total F ⥤ B :=
  associatedFunctor F ⋙
    FilteredComplex.AssociatedSpectralSequence.Total.pageOneSource p q

/-- Total right-derived cohomology of the degree-`p` graded piece in degree `p + q`. -/
@[stacks 0BKK "first-page target functor on total right-derived realizations"]
noncomputable abbrev pageOneTarget (p q : ℤ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ FilteredComplex.gradedPieceFunctor p ⋙
    Functor.RightDerived.Homotopy.cochainCohomologyFunctor F (p + q)

/-- Naturality of the stored first-page comparisons on total right-derived realizations. -/
@[reassoc, stacks 0BKK "naturality of the total right-derived first-page comparison"]
theorem pageOneComparison_naturality (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m ≫ (T.obj.pageOneIso p q).hom =
      (S.obj.pageOneIso p q).hom ≫ (pageOneTarget F p q).map m := sorry

/-- The first-page comparison, natural in total right-derived realizations. -/
@[stacks 0BKK "first-page comparison on total right-derived realizations"]
noncomputable def pageOneComparison (p q : ℤ) :
    pageOneSource F p q ≅ pageOneTarget F p q :=
  NatIso.ofComponents (fun S => S.obj.pageOneIso p q)
    (fun m => pageOneComparison_naturality F p q m)

/-- The first-page source evaluates to the selected page entry. -/
@[simp, stacks 0BKK "first-page source object of a total right-derived realization"]
theorem pageOneSource_obj (p q : ℤ) (S : Realization.Total F) :
    (pageOneSource F p q).obj S = (S.obj.sequence.page 1).X (p, q) := sorry

/-- The first-page source maps by the selected page component. -/
@[simp, stacks 0BKK "first-page source map of a total right-derived realization"]
theorem pageOneSource_map (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m =
      (m.displayed.sequenceMap.hom 1 zero_le_one).f (p, q) := sorry

/-- The first-page target evaluates to total right-derived cohomology of a graded piece. -/
@[simp, stacks 0BKK "first-page target object of a total right-derived realization"]
theorem pageOneTarget_obj (p q : ℤ) (S : Realization.Total F) :
    (pageOneTarget F p q).obj S =
      Functor.RightDerived.Homotopy.cochainCohomology F
        (S.base.gradedPiece p) (p + q) := sorry

/-- The first-page target maps by total right-derived cohomology of the graded-piece map. -/
@[simp, stacks 0BKK "first-page target map of a total right-derived realization"]
theorem pageOneTarget_map (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneTarget F p q).map m =
      Functor.RightDerived.Homotopy.cochainCohomologyMap F
        (FilteredComplex.gradedPieceMap m.base p) (p + q) := sorry

/-- A component of the total first-page comparison is the stored realization comparison. -/
@[simp, stacks 0BKK "component of the total right-derived first-page comparison"]
theorem pageOneComparison_app (p q : ℤ) (S : Realization.Total F) :
    (pageOneComparison F p q).app S = S.obj.pageOneIso p q := sorry

/-- The forward component of the total first-page comparison. -/
@[simp, stacks 0BKK "forward component of the total right-derived first-page comparison"]
theorem pageOneComparison_hom_app (p q : ℤ) (S : Realization.Total F) :
    (pageOneComparison F p q).hom.app S = (S.obj.pageOneIso p q).hom := sorry

/-- The inverse component of the total first-page comparison. -/
@[simp, stacks 0BKK "inverse component of the total right-derived first-page comparison"]
theorem pageOneComparison_inv_app (p q : ℤ) (S : Realization.Total F) :
    (pageOneComparison F p q).inv.app S = (S.obj.pageOneIso p q).inv := sorry

/-- Naturality of the forward total first-page comparison. -/
@[reassoc, stacks 0BKK "forward naturality of the total right-derived first-page comparison"]
theorem pageOneComparison_hom_naturality (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m ≫ (pageOneComparison F p q).hom.app T =
      (pageOneComparison F p q).hom.app S ≫ (pageOneTarget F p q).map m := sorry

/-- Naturality of the inverse total first-page comparison. -/
@[reassoc, stacks 0BKK "inverse naturality of the total right-derived first-page comparison"]
theorem pageOneComparison_inv_naturality (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneTarget F p q).map m ≫ (pageOneComparison F p q).inv.app T =
      (pageOneComparison F p q).inv.app S ≫ (pageOneSource F p q).map m := sorry

/-- Conjugating a target first-page map by the comparison recovers the source page map. -/
@[reassoc, stacks 0BKK "source-map computation for the total right-derived first page"]
theorem pageOneComparison_source_map (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneComparison F p q).hom.app S ≫ (pageOneTarget F p q).map m ≫
        (pageOneComparison F p q).inv.app T =
      (pageOneSource F p q).map m := sorry

/-- Conjugating a source first-page map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 0BKK "target-map computation for the total right-derived first page"]
theorem pageOneComparison_target_map (p q : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneComparison F p q).inv.app S ≫ (pageOneSource F p q).map m ≫
        (pageOneComparison F p q).hom.app T =
      (pageOneTarget F p q).map m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.Total
