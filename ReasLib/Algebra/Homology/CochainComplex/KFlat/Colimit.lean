/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.TermwiseFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.Acyclic.Colimit
public import ReasLib.CategoryTheory.Monoidal.Flat.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of K-flat cochain complexes

@stack 06YR

K-flatness is preserved by a colimit when that colimit is exact and tensoring on the left
preserves it.  Existence of the total tensor product is expressed by the canonical graded-object
owner, independently of how its coproducts are constructed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v uI vI

namespace CochainComplex.IsKFlat

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]

/-- The colimit of K-flat cochain complexes is K-flat when colimits of the indexing shape are
exact and are preserved by tensoring on the left. -/
@[stacks 06YR "exact-colimit form"]
theorem colimit_of_exact (F : I ⥤ CochainComplex C ℤ)
    (hF : ∀ i, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable [HasFilteredColimitsOfSize.{vI, uI} C] [AB5OfSize.{vI, uI} C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]

/-- In an `AB5` setting where tensoring on the left preserves the filtered colimits in question,
a filtered colimit of K-flat cochain complexes is K-flat. -/
@[stacks 06YR "filtered-colimit form"]
theorem colimit_of_isFiltered (F : I ⥤ CochainComplex C ℤ)
    (hF : ∀ i, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end

end CochainComplex.IsKFlat

namespace HomologicalComplex.IsTermwiseFlat

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]

/-- An exact colimit of termwise-flat cochain complexes is termwise flat when tensoring in the
other variable preserves the colimit. -/
@[stacks 06YR "termwise-flat exact-colimit companion"]
theorem colimit_of_exact (F : I ⥤ CochainComplex C ℤ)
    (hF : ∀ i, HomologicalComplex.IsTermwiseFlat (F.obj i)) :
    HomologicalComplex.IsTermwiseFlat (colimit F) := sorry

end

end HomologicalComplex.IsTermwiseFlat

namespace HomologicalComplex.KFlat.termwiseFlat

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]

/-- The exact-colimit closure of K-flat complexes and of termwise-flat complexes combines into
exact-colimit closure of their canonical intersection property. -/
@[stacks 06YR "K-flat termwise-flat exact-colimit form"]
theorem colimit_of_exact (F : I ⥤ CochainComplex C ℤ)
    (hF : ∀ i, HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ) (F.obj i)) :
    HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ) (colimit F) := sorry

/-- K-flat termwise-flat cochain complexes are closed under exact colimits preserved by tensoring
in the varying factor. -/
instance isClosedUnderColimitsOfShape :
    (HomologicalComplex.KFlat.termwiseFlat
      (C := C) (ComplexShape.up ℤ)).IsClosedUnderColimitsOfShape I := sorry

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable [HasFilteredColimitsOfSize.{vI, uI} C] [AB5OfSize.{vI, uI} C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]

/-- A filtered colimit of K-flat termwise-flat cochain complexes is again K-flat and termwise
flat in an `AB5` setting where tensoring preserves the colimit. -/
@[stacks 06YR "K-flat termwise-flat filtered-colimit form"]
theorem colimit_of_isFiltered (F : I ⥤ CochainComplex C ℤ)
    (hF : ∀ i, HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ) (F.obj i)) :
    HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ) (colimit F) := sorry

end

end HomologicalComplex.KFlat.termwiseFlat
