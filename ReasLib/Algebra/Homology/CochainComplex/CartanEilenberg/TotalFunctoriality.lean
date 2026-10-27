/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Total
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal.Axis
public import Mathlib.Data.Int.Interval

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

/-- Extend a finite coproduct by the uniquely determined maps out of zero objects. -/
private theorem MappedTotal.hasCoproduct_of_finite_support
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteCoproducts C]
    {ι : Type*} (X : ι → C) (hfin : {i | ¬ IsZero (X i)}.Finite) :
    HasCoproduct X := by
  classical
  let S := {i : ι // ¬ IsZero (X i)}
  letI : Fintype S := hfin.fintype
  let Y : S → C := fun i => X i.1
  let c : Cofan X := Cofan.mk (∐ Y)
    (fun i => if h : ¬ IsZero (X i) then Sigma.ι Y ⟨i, h⟩ else 0)
  apply HasColimit.mk
  refine ⟨c, Cofan.IsColimit.mk c
    (fun s => Sigma.desc (fun i : S => s.inj i.1)) ?_ ?_⟩
  · intro s i
    change (if h : ¬ IsZero (X i) then (Sigma.ι Y ⟨i, h⟩ : X i ⟶ ∐ Y) else 0) ≫
      Sigma.desc (fun j : S => s.inj j.1) = s.inj i
    by_cases hi : ¬ IsZero (X i)
    · simp only [dif_pos hi, Sigma.ι_desc]
    · exact (not_not.mp hi).eq_of_src _ _
  · intro s m hm
    change (m : (∐ Y) ⟶ s.pt) = Sigma.desc (fun i : S => s.inj i.1)
    apply Sigma.hom_ext (f := Y)
    rintro ⟨i, hi⟩
    rw [Sigma.ι_desc]
    have h := hm i
    change (if h : ¬ IsZero (X i) then
      (Sigma.ι Y ⟨i, h⟩ : X i ⟶ ∐ Y) else 0) ≫ m = s.inj i at h
    rw [dif_pos hi] at h
    exact h

/-- Applying an additive functor termwise preserves the finite antidiagonal support of a
Cartan--Eilenberg double complex. -/
@[stacks 015J "finite support of the mapped Cartan-Eilenberg double complex"]
theorem MappedTotal.support_finite :
    HomologicalComplex₂.AntidiagonalSupport.Finite (I.mapBicomplex F) := by
  obtain ⟨a, ha⟩ := I.horizontalPlus
  letI : CochainComplex.IsStrictlyGE I.bicomplex a := ha
  intro n
  refine (Set.finite_Icc a n).subset ?_
  intro p hp
  change ¬ IsZero (F.obj ((I.bicomplex.X p).X (n - p))) at hp
  constructor
  · by_contra hpa
    have hz := CochainComplex.isZero_of_isStrictlyGE I.bicomplex a p
      (lt_of_not_ge hpa)
    exact hp (F.map_isZero
      ((HomologicalComplex.eval A (up ℤ) (n - p)).map_isZero hz))
  · by_contra hpn
    have hn : n - p < 0 := by omega
    have hz := CochainComplex.isZero_of_isStrictlyGE
      (I.columnResolution p).cochainComplex 0 (n - p) hn
    exact hp (F.map_isZero (hz.of_iso
      ((HomologicalComplex.eval A (up ℤ) (n - p)).mapIso (I.columnIso p).symm)))

/-- The termwise image of a Cartan--Eilenberg double complex has a coproduct total, since its
antidiagonal support remains finite. -/
@[stacks 015J "total existence for the mapped Cartan-Eilenberg double complex"]
instance MappedTotal.hasTotal :
    (I.mapBicomplex F).HasTotal (up ℤ) := by
  intro n
  let T := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let X : T → B := fun ij => ((I.mapBicomplex F).X ij.1.1).X ij.1.2
  change HasCoproduct X
  apply MappedTotal.hasCoproduct_of_finite_support X
  refine Set.Finite.of_injOn (f := fun ij : T => ij.1.1) ?_ ?_
    (MappedTotal.support_finite I F n)
  · intro ij hij
    have hq : n - ij.1.1 = ij.1.2 := by have := ij.2; omega
    change ¬ IsZero (((I.mapBicomplex F).X ij.1.1).X (n - ij.1.1))
    change ¬ IsZero (((I.mapBicomplex F).X ij.1.1).X ij.1.2) at hij
    simpa only [hq] using hij
  · intro ij _ kl _ h
    apply Subtype.ext
    apply Prod.ext h
    have hi : ij.1.1 + ij.1.2 = n := ij.2
    have hk : kl.1.1 + kl.1.2 = n := kl.2
    change ij.1.1 = kl.1.1 at h
    omega

/-- Totalizing the termwise image of a Cartan--Eilenberg double complex agrees canonically with
applying the additive functor to its total complex.

The existence witness for the unmapped total is the identity-functor specialization of
`MappedTotal.hasTotal`; proof irrelevance identifies this total with `Total.complex I`. -/
@[stacks 015H "additive functors and the total Cartan-Eilenberg complex"]
noncomputable def MappedTotal.iso :
    letI : I.bicomplex.HasTotal (up ℤ) := MappedTotal.hasTotal I (𝟭 A)
    (I.mapBicomplex F).total (up ℤ) ≅
      (F.mapHomologicalComplex (up ℤ)).obj (I.bicomplex.total (up ℤ)) := by
  letI : I.bicomplex.HasTotal (up ℤ) := MappedTotal.hasTotal I (𝟭 A)
  exact HomologicalComplex₂.Total.Map.Comparison.iso F I.bicomplex
    (by
      intro n
      have hfin : (I.bicomplex.antidiagonalSupport n).Finite :=
        MappedTotal.support_finite I (𝟭 A) n
      refine (hfin.image (fun p => (p, n - p))).subset ?_
      rintro ⟨p, q⟩ ⟨hpq, hz⟩
      change p + q = n at hpq
      have hq : n - p = q := by omega
      refine ⟨p, ?_, Prod.ext rfl hq⟩
      change ¬ IsZero ((I.bicomplex.X p).X (n - p))
      simpa only [hq] using hz)

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
      (I.mapBicomplex F).total (up ℤ) := by
  letI : I.bicomplex.HasTotal (up ℤ) := MappedTotal.hasTotal I (𝟭 A)
  exact ZeroRow.ToTotal.map ((F.mapHomologicalComplex (up ℤ)).map I.augmentation)
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
