/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Total
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal.Axis

/-!
# Functorial Total Comparisons for Cartan--Eilenberg Resolutions

This file specializes the additive-functor/total comparison to Cartan--Eilenberg resolutions.
It supplies the mapped total automatically and records compatibility with the resolution
augmentation.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable {K : CochainComplex.Plus A} (I : CartanEilenbergResolution K)
variable (F : A ⥤ B) [F.Additive]

/-- Applying an additive functor termwise preserves the finite antidiagonal support of a
Cartan--Eilenberg double complex. -/
@[stacks 015J "finite support of the mapped Cartan-Eilenberg double complex"]
theorem MappedTotal.support_finite :
    HomologicalComplex₂.AntidiagonalSupport.Finite (I.mapBicomplex F) := sorry

/-- The termwise image of a Cartan--Eilenberg double complex has a coproduct total, since its
antidiagonal support remains finite. -/
@[stacks 015J "total existence for the mapped Cartan-Eilenberg double complex"]
instance MappedTotal.hasTotal :
    (I.mapBicomplex F).HasTotal (up ℤ) := sorry

/-- Totalizing the termwise image of a Cartan--Eilenberg double complex agrees canonically with
applying the additive functor to its total complex. -/
@[stacks 015H "additive functors and the total Cartan-Eilenberg complex"]
noncomputable def MappedTotal.iso :
    (I.mapBicomplex F).total (up ℤ) ≅
      (F.mapHomologicalComplex (up ℤ)).obj (Total.complex I) :=
  HomologicalComplex₂.Total.Map.Comparison.iso F I.bicomplex
    (HomologicalComplex₂.AntidiagonalSupport.Finite.toTotalSupport
      (Bicomplex.support_finite I))

/-- On a bidegree summand, the forward mapped-total comparison is the image under `F` of the
corresponding inclusion into the Cartan--Eilenberg total complex. -/
@[reassoc (attr := simp)]
theorem MappedTotal.ι_iso_hom (p q n : ℤ) (h : p + q = n) :
    (I.mapBicomplex F).ιTotal (up ℤ) p q n h ≫
        (MappedTotal.iso I F).hom.f n =
      F.map (I.bicomplex.ιTotal (up ℤ) p q n h) := sorry

/-- The image under `F` of the Cartan--Eilenberg augmentation, extended from the zeroth row to
the total of the mapped double complex. -/
@[stacks 015H "mapped Cartan-Eilenberg augmentation to the total complex with an explicit cycle witness"]
noncomputable def MappedTotal.augmentationOf
    (h_cycles : ∀ p : ℤ, I.augmentation.f p ≫ (I.bicomplex.X p).d 0 1 = 0) :
    (F.mapHomologicalComplex (up ℤ)).obj K.obj ⟶
      (I.mapBicomplex F).total (up ℤ) :=
  ZeroRow.ToTotal.map ((F.mapHomologicalComplex (up ℤ)).map I.augmentation)
    (ZeroRow.ToTotal.Map.cycles F I.augmentation h_cycles)

/-- The image under `F` of the Cartan--Eilenberg augmentation, extended from the zeroth row to
the total of the mapped double complex. -/
@[stacks 015H "mapped Cartan-Eilenberg augmentation to the total complex"]
noncomputable def MappedTotal.augmentation :
    (F.mapHomologicalComplex (up ℤ)).obj K.obj ⟶
      (I.mapBicomplex F).total (up ℤ) :=
  MappedTotal.augmentationOf I F (Augmentation.component_comp_d I)

/-- The mapped augmentation-to-total comparison is compatible with applying `F` to the
unmapped Cartan--Eilenberg augmentation-to-total comparison. -/
@[reassoc]
theorem MappedTotal.augmentation_comp_iso_hom :
    MappedTotal.augmentation I F ≫ (MappedTotal.iso I F).hom =
      (F.mapHomologicalComplex (up ℤ)).map (Total.augmentation I) := sorry

/-- The degree-`n` component of the mapped augmentation-to-total comparison is the mapped
augmentation component followed by the inclusion of bidegree `(n, 0)`. -/
@[simp]
theorem MappedTotal.augmentation_f (n : ℤ) :
    (MappedTotal.augmentation I F).f n =
      F.map (Augmentation.component I n) ≫
        (I.mapBicomplex F).ιTotal (up ℤ) n 0 n (Int.add_zero n) := sorry

end CochainComplex.CartanEilenbergResolution
