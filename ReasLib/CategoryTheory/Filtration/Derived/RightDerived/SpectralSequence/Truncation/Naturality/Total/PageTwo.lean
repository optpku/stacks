module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Naturality

/-!
# Second page on total truncation-filtration realizations

This leaf exposes the source-facing `E₂` entry and its comparison with the pointwise right-derived
functor on cohomology objects.  The indexing is kept in the canonical `(i, j)` form used by the
truncation realization itself.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- The `(i, j)` entry of the renumbered second page on total truncation realizations. -/
@[stacks 0BKM "second-page source functor on total truncation realizations"]
noncomputable def pageTwoSource (i : ℕ) (j : ℤ) :
    Realization.Total F ⥤ B where
  obj S := (S.obj.sequence.page 2).X (Int.ofNat i, j)
  map m := (m.displayed.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j)
  map_id := sorry
  map_comp := sorry

/-- The pointwise right-derived target of the `j`-th cohomology object. -/
@[stacks 0BKM "second-page target functor on total truncation realizations"]
noncomputable abbrev pageTwoTarget (i : ℕ) (j : ℤ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ DerivedCategory.homologyFunctor A j ⋙ F.rightDerived i

/-- Naturality of the stored second-page comparisons on total truncation realizations. -/
@[stacks 0BKM "naturality for total truncation second-page comparisons"]
theorem pageTwoComparison_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoSource F i j).map m ≫ (T.obj.pageTwoIso i j).hom =
      (S.obj.pageTwoIso i j).hom ≫ (pageTwoTarget F i j).map m := sorry

/-- The second-page comparison, natural in a total truncation realization. -/
@[stacks 0BKM "second-page comparison on total truncation realizations"]
noncomputable def pageTwoComparison (i : ℕ) (j : ℤ) :
    pageTwoSource F i j ≅ pageTwoTarget F i j :=
  NatIso.ofComponents (fun S => S.obj.pageTwoIso i j)
    (fun m => pageTwoComparison_naturality F i j m)

/-- The second-page source evaluates to the selected renumbered page entry. -/
@[simp, stacks 0BKM "second-page source object on total truncation realizations"]
theorem pageTwoSource_obj (i : ℕ) (j : ℤ) (S : Realization.Total F) :
    (pageTwoSource F i j).obj S =
      (S.obj.sequence.page 2).X (Int.ofNat i, j) := sorry

/-- The second-page source maps by the selected page component. -/
@[simp, stacks 0BKM "second-page source map on total truncation realizations"]
theorem pageTwoSource_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoSource F i j).map m =
      (m.displayed.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j) := sorry

/-- The second-page target evaluates to the right-derived image of cohomology. -/
@[simp, stacks 0BKM "second-page target object on total truncation realizations"]
theorem pageTwoTarget_obj (i : ℕ) (j : ℤ) (S : Realization.Total F) :
    (pageTwoTarget F i j).obj S =
      (F.rightDerived i).obj ((DerivedCategory.homologyFunctor A j).obj S.base) := sorry

/-- The second-page target maps by the induced derived-category cohomology morphism. -/
@[simp, stacks 0BKM "second-page target map on total truncation realizations"]
theorem pageTwoTarget_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoTarget F i j).map m =
      (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map m.base) := sorry

/-- A second-page comparison component is the isomorphism stored by the realization. -/
@[simp, stacks 0BKM "second-page comparison component on total truncation realizations"]
theorem pageTwoComparison_app (i : ℕ) (j : ℤ) (S : Realization.Total F) :
    (pageTwoComparison F i j).app S = S.obj.pageTwoIso i j := sorry

/-- The forward second-page component is the stored comparison morphism. -/
@[simp, stacks 0BKM "forward second-page comparison component on total truncation realizations"]
theorem pageTwoComparison_hom_app (i : ℕ) (j : ℤ) (S : Realization.Total F) :
    (pageTwoComparison F i j).hom.app S = (S.obj.pageTwoIso i j).hom := sorry

/-- The inverse second-page component is the inverse stored comparison morphism. -/
@[simp, stacks 0BKM "inverse second-page comparison component on total truncation realizations"]
theorem pageTwoComparison_inv_app (i : ℕ) (j : ℤ) (S : Realization.Total F) :
    (pageTwoComparison F i j).inv.app S = (S.obj.pageTwoIso i j).inv := sorry

/-- Naturality of the forward total second-page comparison. -/
@[reassoc, stacks 0BKM "forward naturality of the total truncation second-page comparison"]
theorem pageTwoComparison_hom_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoSource F i j).map m ≫ (pageTwoComparison F i j).hom.app T =
      (pageTwoComparison F i j).hom.app S ≫ (pageTwoTarget F i j).map m := sorry

/-- Naturality of the inverse total second-page comparison. -/
@[reassoc, stacks 0BKM "inverse naturality of the total truncation second-page comparison"]
theorem pageTwoComparison_inv_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoTarget F i j).map m ≫ (pageTwoComparison F i j).inv.app T =
      (pageTwoComparison F i j).inv.app S ≫ (pageTwoSource F i j).map m := sorry

/-- Compute a source page map by conjugating the target map through the comparison. -/
@[reassoc, stacks 0BKM "source map through the total truncation second-page comparison"]
theorem pageTwoComparison_source_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoComparison F i j).hom.app S ≫ (pageTwoTarget F i j).map m ≫
        (pageTwoComparison F i j).inv.app T =
      (pageTwoSource F i j).map m := sorry

/-- Compute a target page map by conjugating the source map through the inverse comparison. -/
@[reassoc, stacks 0BKM "target map through the total truncation second-page comparison"]
theorem pageTwoComparison_target_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoComparison F i j).inv.app S ≫ (pageTwoSource F i j).map m ≫
        (pageTwoComparison F i j).hom.app T =
      (pageTwoTarget F i j).map m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
