module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Total.Functor
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.Total
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.PageOne
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Resolution

/-!
# Functorial First Page of Total Finite Right-Derived Realizations

This leaf assembles the first-page comparisons of finite filtered right-derived realizations into
a natural isomorphism on the total realization category.  Its source is obtained from the generic
realization functor, while its target reuses the functorial `PageOne` owner.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The `(p, q)` entry of the first page, functorial on the total finite realization category. -/
@[stacks 015W "first-page source functor on total finite right-derived realizations"]
noncomputable abbrev pageOneSource
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    Total T ⥤ B :=
  functor T ⋙
    FilteredComplex.SpectralSequence.Realization.pageOneSource p q

/-- Homology of the model graded piece, before comparison with the pointwise derived target. -/
@[stacks 015W "model first-page functor on total finite right-derived realizations"]
noncomputable abbrev pageOneModel
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    Total T ⥤ B :=
  functor T ⋙
    FilteredComplex.SpectralSequence.Realization.pageOneTarget p q

/-- Object computation for the model graded-piece homology functor. -/
@[simp, stacks 015W "model first-page object computation on total finite realizations"]
theorem pageOneModel_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    (S : Total T) :
    (pageOneModel T p q).obj S =
      (S.obj.filtered.gradedPiece p).homology (p + q) := sorry

/-- Morphism computation for the model graded-piece homology functor. -/
@[simp, stacks 015W "model first-page map computation on total finite realizations"]
theorem pageOneModel_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneModel T p q).map m =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap m.displayed.filteredMap p) (p + q) := sorry

/-- The `(p, q)` right-derived first-page target, functorial on the total realization category. -/
@[stacks 015W "first-page target functor on total finite right-derived realizations"]
noncomputable abbrev pageOneTarget
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    Total T ⥤ B :=
  resolutionFunctor T ⋙ Model.GradedPiece.Homology.target T p (p + q)

/-- The generic association comparison, pulled back to total finite realizations. -/
@[stacks 015W "association first-page comparison on total finite realizations"]
noncomputable def associationComparison
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    pageOneSource T p q ≅ pageOneModel T p q :=
  Functor.isoWhiskerLeft (functor T)
    (FilteredComplex.SpectralSequence.Realization.pageOneComparison p q)

/-- The association comparison at an object is the stored first-page association isomorphism. -/
@[simp, stacks 015W "association first-page comparison component"]
theorem associationComparison_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (associationComparison T p q).app S =
      S.obj.association.pageOneIso p q := sorry

/-- The forward association comparison component. -/
@[simp, stacks 015W "forward association first-page comparison component"]
theorem associationComparison_hom_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (associationComparison T p q).hom.app S =
      (S.obj.association.pageOneIso p q).hom := sorry

/-- The inverse association comparison component. -/
@[simp, stacks 015W "inverse association first-page comparison component"]
theorem associationComparison_inv_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (associationComparison T p q).inv.app S =
      (S.obj.association.pageOneIso p q).inv := sorry

/-- The stored graded-piece model comparisons of the realizations are natural along realization
maps: this is the graded-piece square recorded by `Map.comparisonCompatible`. -/
@[reassoc, stacks 015W "naturality of the model first-page comparison on total finite realizations"]
theorem gradedPieceIso_naturality
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneModel T p q).map m ≫ (R.obj.comparison.gradedPieceIso p (p + q)).hom =
      (S.obj.comparison.gradedPieceIso p (p + q)).hom ≫ (pageOneTarget T p q).map m :=
  (m.displayed.comparisonCompatible.gradedPieceSq p (p + q)).w

/-- The model graded-piece homology comparison on total finite realizations, given at each
realization by its own stored graded-piece comparison. -/
@[stacks 015W "model first-page comparison on total finite realizations"]
noncomputable def modelComparison
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    pageOneModel T p q ≅ pageOneTarget T p q :=
  NatIso.ofComponents (fun S ↦ S.obj.comparison.gradedPieceIso p (p + q))
    (gradedPieceIso_naturality T p q)

/-- The model comparison at an object is the selected graded-piece homology isomorphism. -/
@[simp, stacks 015W "model first-page comparison component"]
theorem modelComparison_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (modelComparison T p q).app S =
      S.obj.comparison.gradedPieceIso p (p + q) := rfl

/-- The forward model comparison component. -/
@[simp, stacks 015W "forward model first-page comparison component"]
theorem modelComparison_hom_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (modelComparison T p q).hom.app S =
      (S.obj.comparison.gradedPieceIso p (p + q)).hom := rfl

/-- The inverse model comparison component. -/
@[simp, stacks 015W "inverse model first-page comparison component"]
theorem modelComparison_inv_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (modelComparison T p q).inv.app S =
      (S.obj.comparison.gradedPieceIso p (p + q)).inv := rfl

/-- The first-page comparison, natural in the total finite right-derived realization. -/
@[stacks 015W "first-page comparison on total finite right-derived realizations"]
noncomputable def pageOneComparison
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    pageOneSource T p q ≅ pageOneTarget T p q :=
  associationComparison T p q ≪≫ modelComparison T p q

/-- Object computation for the finite right-derived first-page source. -/
@[simp, stacks 015W "first-page source functor on total finite right-derived realizations"]
theorem pageOneSource_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    (S : Total T) :
    (pageOneSource T p q).obj S = (S.obj.sequence.page 1).X (p, q) := sorry

/-- Morphism computation for the finite right-derived first-page source. -/
@[simp, stacks 015W "first-page source functor on total finite right-derived realizations"]
theorem pageOneSource_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneSource T p q).map m = (m.displayed.sequenceMap.hom 1).f (p, q) := sorry

/-- Object computation for the finite right-derived first-page target. -/
@[simp, stacks 015W "first-page target functor on total finite right-derived realizations"]
theorem pageOneTarget_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    (S : Total T) :
    (pageOneTarget T p q).obj S = PageOne.obj T S.base p q := sorry

/-- Morphism computation for the finite right-derived first-page target. -/
@[simp, stacks 015W "first-page target functor on total finite right-derived realizations"]
theorem pageOneTarget_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneTarget T p q).map m = PageOne.map T m.base p q := sorry

/-- The component of the finite first-page comparison is the realization's stored first-page
isomorphism. -/
@[simp, stacks 015W "first-page comparison on total finite right-derived realizations"]
theorem pageOneComparison_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) (S : Total T) :
    (pageOneComparison T p q).app S = S.obj.pageOneIso p q := rfl

/-- The forward component of the finite first-page comparison is the realization's comparison. -/
@[simp, stacks 015W "first-page comparison on total finite right-derived realizations"]
theorem pageOneComparison_hom_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    (S : Total T) :
    (pageOneComparison T p q).hom.app S = (S.obj.pageOneIso p q).hom := rfl

/-- The inverse component of the finite first-page comparison is the inverse realization
comparison. -/
@[simp, stacks 015W "first-page comparison on total finite right-derived realizations"]
theorem pageOneComparison_inv_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    (S : Total T) :
    (pageOneComparison T p q).inv.app S = (S.obj.pageOneIso p q).inv := rfl

/-- Naturality of the forward finite right-derived first-page comparison. -/
@[reassoc, stacks 015W "naturality of the finite right-derived first-page comparison"]
theorem pageOneComparison_hom_naturality
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneSource T p q).map m ≫ (pageOneComparison T p q).hom.app R =
      (pageOneComparison T p q).hom.app S ≫ (pageOneTarget T p q).map m := sorry

/-- Naturality of the inverse finite right-derived first-page comparison. -/
@[reassoc, stacks 015W "inverse naturality of the finite right-derived first-page comparison"]
theorem pageOneComparison_inv_naturality
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneTarget T p q).map m ≫ (pageOneComparison T p q).inv.app R =
      (pageOneComparison T p q).inv.app S ≫ (pageOneSource T p q).map m := sorry

/-- Compute a first-page source map by conjugating the target map with the comparison. -/
@[reassoc, stacks 015W "source-map computation through the first-page comparison"]
theorem pageOneComparison_source_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneComparison T p q).hom.app S ≫ (pageOneTarget T p q).map m ≫
        (pageOneComparison T p q).inv.app R =
      (pageOneSource T p q).map m := sorry

/-- Compute a first-page target map by conjugating the source map with the inverse comparison. -/
@[reassoc, stacks 015W "target-map computation through the first-page comparison"]
theorem pageOneComparison_target_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (pageOneComparison T p q).inv.app S ≫ (pageOneSource T p q).map m ≫
        (pageOneComparison T p q).hom.app R =
      (pageOneTarget T p q).map m := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization
