module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Total.Functor

/-!
# Functorial Abutment of Total Finite Right-Derived Realizations

This leaf specializes the neutral realization-with-abutment comparison to finite filtered
right-derived spectral sequences.  The source, target, and natural isomorphism are obtained by
composition with `Realization.withAbutmentFunctor`; no second realization or comparison datum is
introduced.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Degree-`n` homology of the finite filtered model, functorial on the total realization
category. -/
@[stacks 015W "abutment source functor on total finite right-derived realizations"]
noncomputable abbrev abutmentSource
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    Total T ⥤ B :=
  withAbutmentFunctor T ⋙
    FilteredComplex.SpectralSequence.Realization.WithAbutment.source
      (Abutment.functor T) n

/-- The degree-`n` right-derived abutment, functorial on the total realization category. -/
@[stacks 015W "abutment target functor on total finite right-derived realizations"]
noncomputable abbrev abutmentTarget
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    Total T ⥤ B :=
  withAbutmentFunctor T ⋙
    FilteredComplex.SpectralSequence.Realization.WithAbutment.target
      (Abutment.functor T) n

/-- The finite right-derived abutment comparison, natural in the total realization. -/
@[stacks 015W "abutment comparison on total finite right-derived realizations"]
noncomputable def abutmentComparison
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    abutmentSource T n ≅ abutmentTarget T n :=
  Functor.isoWhiskerLeft (withAbutmentFunctor T)
    (FilteredComplex.SpectralSequence.Realization.WithAbutment.abutmentComparison
      (Abutment.functor T) n)

/-- Object computation for the finite right-derived abutment source. -/
@[simp, stacks 015W "abutment source functor on total finite right-derived realizations"]
theorem abutmentSource_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (S : Total T) :
    (abutmentSource T n).obj S = S.obj.filtered.underlying.homology n := sorry

/-- Morphism computation for the finite right-derived abutment source. -/
@[simp, stacks 015W "abutment source functor on total finite right-derived realizations"]
theorem abutmentSource_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentSource T n).map m =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.displayed.filteredMap) n := sorry

/-- Object computation for the finite right-derived abutment target. -/
@[simp, stacks 015W "abutment target functor on total finite right-derived realizations"]
theorem abutmentTarget_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (S : Total T) :
    (abutmentTarget T n).obj S = Abutment.obj T S.base n := sorry

/-- Morphism computation for the finite right-derived abutment target. -/
@[simp, stacks 015W "abutment target functor on total finite right-derived realizations"]
theorem abutmentTarget_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentTarget T n).map m = Abutment.map T m.base n := sorry

/-- The component of the finite abutment comparison is the realization's stored target
isomorphism. -/
@[simp, stacks 015W "abutment comparison on total finite right-derived realizations"]
theorem abutmentComparison_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) (S : Total T) :
    (abutmentComparison T n).app S = S.obj.targetIso n := sorry

/-- The forward component of the finite abutment comparison is the realization's comparison. -/
@[simp, stacks 015W "abutment comparison on total finite right-derived realizations"]
theorem abutmentComparison_hom_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (S : Total T) :
    (abutmentComparison T n).hom.app S = (S.obj.targetIso n).hom := sorry

/-- The inverse component of the finite abutment comparison is the inverse realization
comparison. -/
@[simp, stacks 015W "abutment comparison on total finite right-derived realizations"]
theorem abutmentComparison_inv_app
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (S : Total T) :
    (abutmentComparison T n).inv.app S = (S.obj.targetIso n).inv := sorry

/-- Naturality of the forward finite right-derived abutment comparison. -/
@[reassoc, stacks 015W "naturality of the finite right-derived abutment comparison"]
theorem abutmentComparison_hom_naturality
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentSource T n).map m ≫ (abutmentComparison T n).hom.app R =
      (abutmentComparison T n).hom.app S ≫ (abutmentTarget T n).map m := sorry

/-- Naturality of the inverse finite right-derived abutment comparison. -/
@[reassoc, stacks 015W "inverse naturality of the finite right-derived abutment comparison"]
theorem abutmentComparison_inv_naturality
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentTarget T n).map m ≫ (abutmentComparison T n).inv.app R =
      (abutmentComparison T n).inv.app S ≫ (abutmentSource T n).map m := sorry

/-- Compute an abutment source map by conjugating the target map with the comparison. -/
@[reassoc, stacks 015W "source-map computation through the abutment comparison"]
theorem abutmentComparison_source_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentComparison T n).hom.app S ≫ (abutmentTarget T n).map m ≫
        (abutmentComparison T n).inv.app R =
      (abutmentSource T n).map m := sorry

/-- Compute an abutment target map by conjugating the source map with the inverse comparison. -/
@[reassoc, stacks 015W "target-map computation through the abutment comparison"]
theorem abutmentComparison_target_map
    (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {S R : Total T} (m : S ⟶ R) :
    (abutmentComparison T n).inv.app S ≫ (abutmentSource T n).map m ≫
        (abutmentComparison T n).hom.app R =
      (abutmentTarget T n).map m := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization
