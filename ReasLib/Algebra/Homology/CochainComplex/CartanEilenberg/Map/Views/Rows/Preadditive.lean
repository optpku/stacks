/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Rows

/-!
# Additive rowwise views of Cartan--Eilenberg resolution maps

The maps induced on row cycles, differential images, and homology preserve the additive
operations on resolution maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

private theorem imageMap_ι {ι : Type*} {c : ComplexShape ι}
    {C D : HomologicalComplex A c} (φ : C ⟶ D) (i j : ι) :
    HomologicalComplex.imageMap φ i j ≫ image.ι (D.d i j) =
      image.ι (C.d i j) ≫ φ.f j :=
  image.map_ι (Arrow.homMk' (φ.f i) (φ.f j) (φ.comm i j))

/-- Row-cycles maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-cycles map of a Cartan-Eilenberg resolution"]
theorem cyclesRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    cyclesRow (zero : Map I J) q p = 0 := by
  change HomologicalComplex.cyclesMap (0 : I.row q ⟶ J.row q) p = 0
  exact HomologicalComplex.cyclesMap_zero _ _ _

/-- Row-cycles maps preserve addition. -/
@[simp]
theorem cyclesRow_add (f g : Map I J) (q p : ℤ) :
    cyclesRow (f + g) q p = cyclesRow f q p + cyclesRow g q p := by
  change HomologicalComplex.cyclesMap (row f q + row g q) p =
    HomologicalComplex.cyclesMap (row f q) p + HomologicalComplex.cyclesMap (row g q) p
  apply (cancel_mono ((J.row q).iCycles p)).1
  simp only [Preadditive.add_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.add_f_apply, Preadditive.comp_add]

/-- Row-cycles maps preserve additive inverses. -/
@[simp]
theorem cyclesRow_neg (f : Map I J) (q p : ℤ) :
    cyclesRow (-f) q p = -cyclesRow f q p := by
  change HomologicalComplex.cyclesMap (-row f q) p =
    -HomologicalComplex.cyclesMap (row f q) p
  apply (cancel_mono ((J.row q).iCycles p)).1
  simp only [Preadditive.neg_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.neg_f_apply, Preadditive.comp_neg]

/-- Row-cycles maps preserve subtraction. -/
@[simp]
theorem cyclesRow_sub (f g : Map I J) (q p : ℤ) :
    cyclesRow (f - g) q p = cyclesRow f q p - cyclesRow g q p := by
  change HomologicalComplex.cyclesMap (row f q - row g q) p =
    HomologicalComplex.cyclesMap (row f q) p - HomologicalComplex.cyclesMap (row g q) p
  apply (cancel_mono ((J.row q).iCycles p)).1
  simp only [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.sub_f_apply, Preadditive.comp_sub]

/-- Row-cycles maps preserve natural-number scalar multiplication. -/
@[simp]
theorem cyclesRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    cyclesRow (n • f) q p = n • cyclesRow f q p := by
  change HomologicalComplex.cyclesMap (n • row f q) p =
    n • HomologicalComplex.cyclesMap (row f q) p
  apply (cancel_mono ((J.row q).iCycles p)).1
  simp only [Preadditive.nsmul_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.nsmul_f_apply, Preadditive.comp_nsmul]

/-- Row-cycles maps preserve integer scalar multiplication. -/
@[simp]
theorem cyclesRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    cyclesRow (n • f) q p = n • cyclesRow f q p := by
  change HomologicalComplex.cyclesMap (n • row f q) p =
    n • HomologicalComplex.cyclesMap (row f q) p
  apply (cancel_mono ((J.row q).iCycles p)).1
  simp only [Preadditive.zsmul_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.zsmul_f_apply, Preadditive.comp_zsmul]

/-- Row-image maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-image map of a Cartan-Eilenberg resolution"]
theorem imageRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    imageRow (zero : Map I J) q p = 0 := by
  change HomologicalComplex.imageMap (0 : I.row q ⟶ J.row q) p (p + 1) = 0
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [imageMap_ι,
    HomologicalComplex.zero_f_apply, comp_zero, zero_comp]

/-- Row-image maps preserve addition. -/
@[simp]
theorem imageRow_add (f g : Map I J) (q p : ℤ) :
    imageRow (f + g) q p = imageRow f q p + imageRow g q p := by
  change HomologicalComplex.imageMap (row f q + row g q) p (p + 1) =
    HomologicalComplex.imageMap (row f q) p (p + 1) +
      HomologicalComplex.imageMap (row g q) p (p + 1)
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [Preadditive.add_comp, imageMap_ι,
    HomologicalComplex.add_f_apply, Preadditive.comp_add]

/-- Row-image maps preserve additive inverses. -/
@[simp]
theorem imageRow_neg (f : Map I J) (q p : ℤ) :
    imageRow (-f) q p = -imageRow f q p := by
  change HomologicalComplex.imageMap (-row f q) p (p + 1) =
    -HomologicalComplex.imageMap (row f q) p (p + 1)
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [Preadditive.neg_comp, imageMap_ι,
    HomologicalComplex.neg_f_apply, Preadditive.comp_neg]

/-- Row-image maps preserve subtraction. -/
@[simp]
theorem imageRow_sub (f g : Map I J) (q p : ℤ) :
    imageRow (f - g) q p = imageRow f q p - imageRow g q p := by
  change HomologicalComplex.imageMap (row f q - row g q) p (p + 1) =
    HomologicalComplex.imageMap (row f q) p (p + 1) -
      HomologicalComplex.imageMap (row g q) p (p + 1)
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [Preadditive.sub_comp, imageMap_ι,
    HomologicalComplex.sub_f_apply, Preadditive.comp_sub]

/-- Row-image maps preserve natural-number scalar multiplication. -/
@[simp]
theorem imageRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    imageRow (n • f) q p = n • imageRow f q p := by
  change HomologicalComplex.imageMap (n • row f q) p (p + 1) =
    n • HomologicalComplex.imageMap (row f q) p (p + 1)
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [Preadditive.nsmul_comp, imageMap_ι,
    HomologicalComplex.nsmul_f_apply, Preadditive.comp_nsmul]

/-- Row-image maps preserve integer scalar multiplication. -/
@[simp]
theorem imageRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    imageRow (n • f) q p = n • imageRow f q p := by
  change HomologicalComplex.imageMap (n • row f q) p (p + 1) =
    n • HomologicalComplex.imageMap (row f q) p (p + 1)
  apply (cancel_mono (image.ι ((J.row q).d p (p + 1)))).1
  simp only [Preadditive.zsmul_comp, imageMap_ι,
    HomologicalComplex.zsmul_f_apply, Preadditive.comp_zsmul]

/-- Row-homology maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-homology map of a Cartan-Eilenberg resolution"]
theorem homologyRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    homologyRow (zero : Map I J) q p = 0 := by
  change HomologicalComplex.homologyMap (0 : I.row q ⟶ J.row q) p = 0
  exact HomologicalComplex.homologyMap_zero _ _ _

/-- Row-homology maps preserve addition. -/
@[simp]
theorem homologyRow_add (f g : Map I J) (q p : ℤ) :
    homologyRow (f + g) q p = homologyRow f q p + homologyRow g q p := by
  change HomologicalComplex.homologyMap (row f q + row g q) p =
    HomologicalComplex.homologyMap (row f q) p + HomologicalComplex.homologyMap (row g q) p
  exact HomologicalComplex.homologyMap_add _ _ _

/-- Row-homology maps preserve additive inverses. -/
@[simp]
theorem homologyRow_neg (f : Map I J) (q p : ℤ) :
    homologyRow (-f) q p = -homologyRow f q p := by
  change HomologicalComplex.homologyMap (-row f q) p =
    -HomologicalComplex.homologyMap (row f q) p
  exact HomologicalComplex.homologyMap_neg _ _

/-- Row-homology maps preserve subtraction. -/
@[simp]
theorem homologyRow_sub (f g : Map I J) (q p : ℤ) :
    homologyRow (f - g) q p = homologyRow f q p - homologyRow g q p := by
  change HomologicalComplex.homologyMap (row f q - row g q) p =
    HomologicalComplex.homologyMap (row f q) p - HomologicalComplex.homologyMap (row g q) p
  exact HomologicalComplex.homologyMap_sub _ _ _

/-- Row-homology maps preserve natural-number scalar multiplication. -/
@[simp]
theorem homologyRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    homologyRow (n • f) q p = n • homologyRow f q p := by
  change (HomologicalComplex.homologyFunctor A (up ℤ) p).map (n • row f q) =
    n • (HomologicalComplex.homologyFunctor A (up ℤ) p).map (row f q)
  exact (HomologicalComplex.homologyFunctor A (up ℤ) p).map_nsmul

/-- Row-homology maps preserve integer scalar multiplication. -/
@[simp]
theorem homologyRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    homologyRow (n • f) q p = n • homologyRow f q p := by
  change (HomologicalComplex.homologyFunctor A (up ℤ) p).map (n • row f q) =
    n • (HomologicalComplex.homologyFunctor A (up ℤ) p).map (row f q)
  exact (HomologicalComplex.homologyFunctor A (up ℤ) p).map_zsmul

end CochainComplex.CartanEilenbergResolution.Map
