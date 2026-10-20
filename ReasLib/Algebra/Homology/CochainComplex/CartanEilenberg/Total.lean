/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Properties
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison.QuasiIso
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalSupport

/-!
# Total Complex of a Cartan--Eilenberg Resolution

The Cartan--Eilenberg augmentation lands in the zeroth vertical cycles and therefore extends to
the total complex.  This file exposes that comparison, its quasi-isomorphism property, and the
resulting cochain-complex injective resolution whose target is the actual total complex.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- Finite antidiagonal support gives every Cartan--Eilenberg double complex its canonical
coproduct total. -/
@[stacks 015H "total existence for a Cartan-Eilenberg double complex"]
instance Bicomplex.hasTotal (I : CartanEilenbergResolution K) :
    I.bicomplex.HasTotal (up ℤ) := sorry

variable (I : CartanEilenbergResolution K)

/-- The total cochain complex underlying a Cartan--Eilenberg resolution. -/
@[stacks 015H "the total Cartan-Eilenberg complex"]
abbrev Total.complex : CochainComplex A ℤ :=
  I.bicomplex.total (up ℤ)

/-- The canonical map from `K.obj.X p` to the vertical cycles in degree zero of the `p`-th
Cartan--Eilenberg column. -/
@[stacks 015H "Cartan-Eilenberg augmentation into column cycles with an explicit cycle witness"]
noncomputable def Total.cyclesMapOf
    (h_cycles : ∀ p : ℤ, I.augmentation.f p ≫ (I.bicomplex.X p).d 0 1 = 0) (p : ℤ) :
    K.obj.X p ⟶ (I.column p).cycles 0 :=
  ZeroRow.Cycles.map I.augmentation h_cycles p

/-- The canonical map from `K.obj.X p` to the vertical cycles in degree zero of the `p`-th
Cartan--Eilenberg column. -/
@[stacks 015H "Cartan-Eilenberg augmentation into column cycles"]
noncomputable def Total.cyclesMap (p : ℤ) :
    K.obj.X p ⟶ (I.column p).cycles 0 :=
  Total.cyclesMapOf I (Augmentation.component_comp_d I) p

/-- Composing the Cartan--Eilenberg cycle map with the cycle inclusion recovers the original
augmentation component. -/
@[reassoc (attr := simp)]
theorem Total.cyclesMap_iCycles (p : ℤ) :
    Total.cyclesMap I p ≫ (I.column p).iCycles 0 = Augmentation.component I p := sorry

/-- The Cartan--Eilenberg augmentation identifies each term of the source with the degree-zero
vertical cycles of the corresponding column. -/
@[stacks 015H "Cartan-Eilenberg augmentation isomorphism on column cycles"]
instance Total.cyclesMap_isIso (p : ℤ) :
    IsIso (Total.cyclesMap I p) := sorry

/-- The Cartan--Eilenberg augmentation, extended canonically from the zeroth row to the total
complex. -/
@[stacks 015H "Cartan-Eilenberg augmentation to the total complex with an explicit cycle witness"]
noncomputable def Total.augmentationOf
    (h_cycles : ∀ p : ℤ, I.augmentation.f p ≫ (I.bicomplex.X p).d 0 1 = 0) :
    K.obj ⟶ Total.complex I :=
  ZeroRow.ToTotal.map I.augmentation h_cycles

/-- The Cartan--Eilenberg augmentation, extended canonically from the zeroth row to the total
complex. -/
@[stacks 015H "the Cartan-Eilenberg augmentation to the total complex"]
noncomputable def Total.augmentation : K.obj ⟶ Total.complex I :=
  Total.augmentationOf I (Augmentation.component_comp_d I)

/-- In degree `n`, the Cartan--Eilenberg map to the total complex is the augmentation component
followed by the inclusion of bidegree `(n, 0)`. -/
@[simp]
theorem Total.augmentation_f (n : ℤ) :
    (Total.augmentation I).f n =
      Augmentation.component I n ≫ I.bicomplex.ιTotal (up ℤ) n 0 n (Int.add_zero n) := sorry

/-- The map from a bounded-below complex to the total complex of its Cartan--Eilenberg
resolution is a quasi-isomorphism. -/
@[stacks 015H "the total Cartan-Eilenberg comparison is a quasi-isomorphism"]
theorem Total.augmentation_quasiIso :
    QuasiIso (Total.augmentation I) := sorry

/-- The total complex of a Cartan--Eilenberg resolution is bounded below. -/
@[stacks 015H "boundedness of the total Cartan-Eilenberg complex"]
theorem Total.plus : CochainComplex.plus A (Total.complex I) := sorry

/-- Every term of the total complex of a Cartan--Eilenberg resolution is injective. -/
@[stacks 015H "termwise injectivity of the total Cartan-Eilenberg complex"]
instance Total.isInjective (n : ℤ) : Injective ((Total.complex I).X n) := sorry

/-- The total complex of a Cartan--Eilenberg resolution, bundled as a bounded-below complex. -/
@[stacks 015H "the bounded-below total Cartan-Eilenberg complex with an explicit bound"]
noncomputable def Total.toPlusOf (h_plus : CochainComplex.plus A (Total.complex I)) :
    CochainComplex.Plus A :=
  ⟨Total.complex I, h_plus⟩

/-- The total complex of a Cartan--Eilenberg resolution, bundled as a bounded-below complex. -/
@[stacks 015H "the bounded-below total Cartan-Eilenberg complex"]
noncomputable def Total.toPlus : CochainComplex.Plus A :=
  Total.toPlusOf I (Total.plus I)

/-- Forgetting the bounded-below packaging of `Total.toPlus` recovers the actual total
complex. -/
@[simp]
theorem Total.toPlus_coe : (Total.toPlus I).obj = Total.complex I := sorry

/-- The total complex of a Cartan--Eilenberg resolution, bundled as a bounded-below complex of
injective objects. -/
@[stacks 015H "the injective bounded-below total Cartan-Eilenberg complex with explicit certificates"]
noncomputable def Total.toInjectivePlusOf
    (h_plus : CochainComplex.plus A (Total.complex I))
    (h_injective : ∀ n : ℤ, Injective ((Total.complex I).X n)) :
    CochainComplex.InjectivePlus A :=
  ⟨Total.toPlusOf I h_plus, h_injective⟩

/-- The total complex of a Cartan--Eilenberg resolution, bundled as a bounded-below complex of
injective objects. -/
@[stacks 015H "the injective bounded-below total Cartan-Eilenberg complex"]
noncomputable def Total.toInjectivePlus : CochainComplex.InjectivePlus A :=
  Total.toInjectivePlusOf I (Total.plus I) (Total.isInjective I)

/-- Forgetting the termwise-injective packaging recovers the actual total complex. -/
@[simp]
theorem Total.toInjectivePlus_coe :
    (Total.toInjectivePlus I : CochainComplex A ℤ) = Total.complex I := sorry

/-- The total complex of a Cartan--Eilenberg resolution, together with its canonical
quasi-isomorphism from the original complex, is an injective resolution of cochain complexes. -/
@[stacks 015H "the total Cartan-Eilenberg injective resolution with explicit certificates"]
noncomputable def Total.toInjectiveResolutionOf
    (h_plus : CochainComplex.plus A (Total.complex I))
    (h_injective : ∀ n : ℤ, Injective ((Total.complex I).X n))
    (h_cycles : ∀ p : ℤ, I.augmentation.f p ≫ (I.bicomplex.X p).d 0 1 = 0)
    (h_quasiIso : QuasiIso (Total.augmentationOf I h_cycles)) :
    CochainComplex.InjectiveResolution K.obj :=
  CochainComplex.InjectiveResolution.mk (Total.toInjectivePlusOf I h_plus h_injective)
    (Total.augmentationOf I h_cycles) h_quasiIso

/-- The total complex of a Cartan--Eilenberg resolution, together with its canonical
quasi-isomorphism from the original complex, is an injective resolution of cochain complexes. -/
@[stacks 015H "the total complex of a Cartan-Eilenberg resolution"]
noncomputable def Total.toInjectiveResolution :
    CochainComplex.InjectiveResolution K.obj :=
  Total.toInjectiveResolutionOf I (Total.plus I) (Total.isInjective I)
    (Augmentation.component_comp_d I) (Total.augmentation_quasiIso I)

/-- The target of `Total.toInjectiveResolution`, after forgetting its packaging, is the actual
total complex. -/
@[simp]
theorem Total.toInjectiveResolution_coe :
    (Total.toInjectiveResolution I : CochainComplex A ℤ) = Total.complex I := sorry

/-- The comparison map in `Total.toInjectiveResolution` is the Cartan--Eilenberg augmentation to
the total complex. -/
@[simp]
theorem Total.toInjectiveResolution_ι :
    (Total.toInjectiveResolution I).ι = Total.augmentation I := sorry

/-- The degreewise comparison map in `Total.toInjectiveResolution` is the augmentation component
followed by the corresponding total-complex inclusion. -/
@[simp]
theorem Total.toInjectiveResolution_ι_f (n : ℤ) :
    (Total.toInjectiveResolution I).ι.f n =
      Augmentation.component I n ≫ I.bicomplex.ιTotal (up ℤ) n 0 n (Int.add_zero n) := sorry

section InstanceChecks

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}
variable (I : CartanEilenbergResolution K)

#synth Injective ((Total.complex I).X 0)

end InstanceChecks

end CochainComplex.CartanEilenbergResolution
