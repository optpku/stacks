/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Functor
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total.Forget
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment.Displayed

/-!
# Abutment Comparison for Total Grothendieck Spectral Sequences

This leaf forgets page-two-specific data to the neutral functorial-abutment total category and
pulls its canonical abutment comparison back to total Grothendieck realizations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

/-- Forget the Grothendieck page-two data and view a total realization in the generic
functorial-abutment total category.  The specialized total category retains page-two data, while
this projection exposes the neutral `WithAbutment` owner for generic constructions. -/
@[stacks 015N "generic functorial-abutment presentation of a total Grothendieck spectral sequence"]
noncomputable def toAbutmentTotal
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) :
    Total G RF RGF ⥤
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Total
        (abutmentFunctor RGF) where
  obj S := ⟨S.base, S.toWithAbutment⟩
  map f := ⟨f.base, Total.Hom.toWithAbutmentMap f⟩
  map_id := sorry
  map_comp := sorry

/-- The generic abutment total projection preserves the supporting derived object. -/
@[simp, stacks 015N "base object of the generic abutment total projection"]
theorem toAbutmentTotal_obj_base
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (S : Total G RF RGF) :
    ((toAbutmentTotal G RF RGF).obj S).base = S.base := sorry

/-- The generic abutment total projection retains the underlying `WithAbutment` realization. -/
@[simp, stacks 015N "object of the generic abutment total projection"]
theorem toAbutmentTotal_obj_obj
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (S : Total G RF RGF) :
    ((toAbutmentTotal G RF RGF).obj S).obj = S.toWithAbutment := sorry

/-- The generic abutment total projection preserves the underlying derived-category arrow. -/
@[simp, stacks 015N "base map of the generic abutment total projection"]
theorem toAbutmentTotal_map_base
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    ((toAbutmentTotal G RF RGF).map f).base = f.base := sorry

/-- The generic abutment total projection retains the generic functorial-abutment map. -/
@[simp, stacks 015N "map of the generic abutment total projection"]
theorem toAbutmentTotal_map_map
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    ((toAbutmentTotal G RF RGF).map f).displayed =
      Total.Hom.toWithAbutmentMap f := sorry

/-- Degree-`n` cohomology of the underlying filtered complex, functorial in a total
Grothendieck spectral-sequence realization. -/
@[stacks 015N "abutment source functor on total Grothendieck spectral sequences"]
noncomputable def abutmentSource
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ) :
    Total G RF RGF ⥤ C :=
  { obj := fun S => S.realization.filtered.underlying.homology n
    map := fun f =>
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap f.map.filteredMap) n
    map_id := sorry
    map_comp := sorry }

/-- Evaluation of `abutmentSource` returns cohomology of the underlying filtered
complex. -/
@[simp, stacks 015N "abutment source functor on total Grothendieck spectral sequences"]
theorem abutmentSource_obj
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    (S : Total G RF RGF) :
    (abutmentSource G RF RGF n).obj S =
      S.realization.filtered.underlying.homology n := sorry

/-- The morphism action of `abutmentSource` is the induced map on cohomology of
underlying filtered complexes. -/
@[simp, stacks 015N "abutment source functor on total Grothendieck spectral sequences"]
theorem abutmentSource_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (abutmentSource G RF RGF n).map f =
      HomologicalComplex.homologyMap (FilteredComplex.underlyingMap f.map.filteredMap) n := sorry

/-- The abutment source map can be read through the generic functorial-abutment map owner. -/
@[simp, stacks 015N "generic abutment source map on total Grothendieck spectral sequences"]
theorem abutmentSource_map_toWithAbutmentMap
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (abutmentSource G RF RGF n).map f =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap
          (Total.Hom.toWithAbutmentMap f).filteredMap) n := sorry

/-- Naturality of the abutment comparison across a total morphism. -/
@[reassoc, stacks 015N "naturality of the abutment comparison on total Grothendieck spectral sequences"]
theorem abutmentComparison_naturality
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (abutmentSource G RF RGF n).map f ≫ (T.realization.abutmentIso n).hom =
    (S.realization.abutmentIso n).hom ≫
        ((forgetBase ⋙ abutmentFunctor RGF n).map f) := sorry

/-- Naturality of the inverse abutment comparison across a total morphism. -/
@[reassoc, stacks 015N "inverse naturality of the abutment comparison on total Grothendieck spectral sequences"]
theorem abutmentComparison_inv_naturality
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    ((forgetBase ⋙ abutmentFunctor RGF n).map f) ≫
        (T.realization.abutmentIso n).inv =
      (S.realization.abutmentIso n).inv ≫
        (abutmentSource G RF RGF n).map f := sorry

/-- Pull back the neutral generic functorial-abutment comparison to the Grothendieck total
category. -/
@[stacks 015N "generic abutment comparison on total Grothendieck spectral sequences"]
noncomputable def genericAbutmentComparison
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ) :
    abutmentSource G RF RGF n ≅ forgetBase ⋙ abutmentFunctor RGF n :=
  Functor.isoWhiskerLeft (toAbutmentTotal G RF RGF)
    (FilteredComplex.SpectralSequence.Realization.WithAbutment.abutmentComparison
      (abutmentFunctor RGF) n)

/-- The public Grothendieck abutment comparison is the generic functorial-abutment comparison
pulled back along `toAbutmentTotal`. -/
@[stacks 015N "abutment comparison on total Grothendieck spectral sequences"]
noncomputable abbrev abutmentComparison
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ) :
    abutmentSource G RF RGF n ≅ forgetBase ⋙ abutmentFunctor RGF n :=
  genericAbutmentComparison G RF RGF n

/-- The forward component of `abutmentComparison` is the comparison stored in the
realization. -/
@[simp, stacks 015N "abutment comparison on total Grothendieck spectral sequences"]
theorem abutmentComparison_hom_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    (S : Total G RF RGF) :
    (abutmentComparison G RF RGF n).hom.app S =
      (S.realization.abutmentIso n).hom := sorry

/-- The inverse component of `abutmentComparison` is the inverse comparison stored in the
realization. -/
@[simp, stacks 015N "abutment comparison on total Grothendieck spectral sequences"]
theorem abutmentComparison_inv_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    (S : Total G RF RGF) :
    (abutmentComparison G RF RGF n).inv.app S =
      (S.realization.abutmentIso n).inv := sorry

/-- The complete abutment comparison component is the isomorphism stored by the realization. -/
@[simp, stacks 015N "abutment comparison component on total Grothendieck spectral sequences"]
theorem abutmentComparison_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    (S : Total G RF RGF) :
    (abutmentComparison G RF RGF n).app S = S.realization.abutmentIso n := sorry

/-- Conjugating a target abutment map by the comparison recovers the source map. -/
@[reassoc, stacks 015N "source-map computation for the total Grothendieck abutment"]
theorem abutmentComparison_source_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (abutmentComparison G RF RGF n).hom.app S ≫
        ((forgetBase ⋙ abutmentFunctor RGF n).map f) ≫
        (abutmentComparison G RF RGF n).inv.app T =
      (abutmentSource G RF RGF n).map f := sorry

/-- Conjugating a source abutment map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 015N "target-map computation for the total Grothendieck abutment"]
theorem abutmentComparison_target_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (abutmentComparison G RF RGF n).inv.app S ≫
        (abutmentSource G RF RGF n).map f ≫
        (abutmentComparison G RF RGF n).hom.app T =
      ((forgetBase ⋙ abutmentFunctor RGF n).map f) := sorry

/- Axiom audit: the total projection and source functor carry explicit data.  The comparison
isomorphism is pulled back from the neutral `WithAbutment` owner; `sorryAx` is confined to functor
laws, naturality, and component-computation propositions. -/

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total
