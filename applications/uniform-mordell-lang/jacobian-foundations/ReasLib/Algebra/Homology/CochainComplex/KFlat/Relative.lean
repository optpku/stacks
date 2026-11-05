module

public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative K-flat homological complexes

This file exposes cochain-complex and homotopy-category specializations of the shape-general
notion in `HomologicalComplex.KFlat.Relative`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CochainComplex

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]

/-- Relative K-flatness of a cochain complex for a bifunctor. -/
abbrev IsKFlatFor (K : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] : Prop :=
  HomologicalComplex.IsKFlatFor K F (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- An acyclic input remains acyclic after totalized application of a bifunctor to a cochain
complex that is K-flat for that bifunctor. -/
lemma IsKFlatFor.acyclic_mapBifunctor {K : CochainComplex C₂ ℤ}
    {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms]
    [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] (hK : K.IsKFlatFor F)
    {M : CochainComplex C₁ ℤ}
    [HomologicalComplex.HasMapBifunctor M K F (ComplexShape.up ℤ)]
    (hM : M.Acyclic) :
    (HomologicalComplex.mapBifunctor M K F (ComplexShape.up ℤ)).Acyclic := sorry

/-- Relative K-flatness of a cochain complex is preservation of acyclicity by the associated
totalized bifunctor. -/
theorem isKFlatFor_iff (K : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] :
    K.IsKFlatFor F ↔
      ∀ ⦃M : CochainComplex C₁ ℤ⦄
        [HomologicalComplex.HasMapBifunctor M K F (ComplexShape.up ℤ)],
          M.Acyclic →
            (HomologicalComplex.mapBifunctor M K F (ComplexShape.up ℤ)).Acyclic := sorry

end CochainComplex
