/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived localization of good flat models

K-flat homotopy objects represented by complexes with flat terms form the good-model category
used for unbounded derived functors. This file relates that smaller category to the canonical
K-flat localization without introducing a second derived category.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.KFlat.TermwiseFlat

section Inclusion

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The canonical inclusion of K-flat homotopy objects with flat terms into all K-flat
homotopy objects. -/
@[stacks 06YS "good flat models into K-flat models"]
abbrev toKFlat :
    HomotopyCategory.KFlat.TermwiseFlat C ⥤ HomotopyCategory.KFlat C :=
  ObjectProperty.ιOfLE (fun _ hK ↦ hK.1)

/-- Including a good flat model first among K-flat objects and then in the homotopy category
agrees with the direct full-subcategory inclusion. -/
@[stacks 06YS "good flat model inclusion comparison"]
def toKFlatCompιIso :
    toKFlat (C := C) ⋙ (HomotopyCategory.kFlat C).ι ≅
      (HomotopyCategory.KFlat.termwiseFlat C).ι :=
  ObjectProperty.ιOfLECompιIso (fun _ hK ↦ hK.1)

end Inclusion

section Localization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- Localization of good flat models into the derived category, through the canonical K-flat
localization model. -/
@[stacks 06YS "good flat model localization"]
noncomputable abbrev localizationFunctor :
    HomotopyCategory.KFlat.TermwiseFlat C ⥤ DerivedCategory C :=
  toKFlat (C := C) ⋙ DerivedCategory.KFlat.localizationFunctor (C := C)

/-- The good-flat-model localization agrees with direct inclusion followed by the standard
homotopy-to-derived localization. -/
@[stacks 06YS "good flat model localization comparison"]
noncomputable def localizationFunctorIso :
    localizationFunctor (C := C) ≅
      (HomotopyCategory.KFlat.termwiseFlat C).ι ⋙
        (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (toKFlatCompιIso (C := C)) _

/-- The exact condition that localization of good flat models presents the derived category. -/
@[stacks 06YS "good flat model localization condition"]
abbrev IsLocalization : Prop :=
  (localizationFunctor (C := C)).IsLocalization
    (HomotopyCategory.KFlat.TermwiseFlat.quasiIso C)

/-- A denominator cover by K-flat complexes with flat terms makes their canonical functor to the
derived category a localization. This remains a theorem rather than an instance while its proof
is deferred, because localization structures select downstream data. -/
@[stacks 06YS "good flat models present the derived category"]
theorem localizationIsLocalization
    [HomotopyCategory.KFlat.TermwiseFlat.HasResolutions C] :
    IsLocalization (C := C) := sorry

end Localization

section Monoidal

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [MonoidalCategory.IsFlat.Coproducts C]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [HomotopyCategory.KFlat.TensorDescends (C := C)]
variable [DerivedCategory.KFlat.IsLocalization (C := C)]

#synth (toKFlat (C := C)).Monoidal
#synth (localizationFunctor (C := C)).Monoidal

end Monoidal

end CategoryTheory.DerivedCategory.KFlat.TermwiseFlat
