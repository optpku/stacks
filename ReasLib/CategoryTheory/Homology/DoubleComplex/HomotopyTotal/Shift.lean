/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplexShift
public import ReasLib.CategoryTheory.Homology.DoubleComplex.HomotopyTotal.Basic

/-!
# Shift compatibility of totalization on homotopy categories

The total complex commutes with the shift in the outer cochain-complex direction. This file
packages the objectwise comparison as a natural isomorphism, records its coherence, and descends
the resulting `CommShift` structures to homotopy categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory

noncomputable section

universe v u

namespace HomologicalComplex₂.HomotopyTotal

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasCountableCoproducts C]

namespace rawDirect

/-- The natural comparison between shifting a double complex in its outer direction before
totalization and shifting its total complex. -/
noncomputable def shiftIso (n : ℤ) :
    shiftFunctor (HomologicalComplex₂ C (up ℤ) (up ℤ)) n ⋙ rawDirect C ≅
      rawDirect C ⋙ shiftFunctor (CochainComplex C ℤ) n :=
  NatIso.ofComponents (fun K => K.totalShift₁Iso n)
    (fun f => totalShift₁Iso_hom_naturality f n)

/-- Total-complex inclusions commute with transport in the first and total degrees. -/
private theorem ιTotal_congr (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    {p p' q n n' : ℤ} (hp : p = p') (hn : n' = n)
    (h : p + q = n) (h' : p' + q = n') :
    K.ιTotal (up ℤ) p q n h =
      (HomologicalComplex.XIsoOfEq K hp).hom.f q ≫
        K.ιTotal (up ℤ) p' q n' h' ≫ ((K.total (up ℤ)).XIsoOfEq hn).hom := by
  subst p' n'
  simp [HomologicalComplex.XIsoOfEq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The totalization shift comparison at zero is the canonical zero-shift comparison. -/
theorem shiftIso_zero :
    shiftIso C 0 = Functor.CommShift.isoZero (rawDirect C) ℤ := by
  ext K n
  simp only [Functor.CommShift.isoZero_hom_app]
  dsimp [shiftIso, rawDirect]
  apply total.hom_ext
  intro p q h
  rw [K.ι_totalShift₁Iso_hom_f 0 p q n h _ rfl _ rfl, ιTotal_map_assoc,
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorZero_inv_app_f]
  dsimp [shiftFunctor₁XXIso]
  simp only [Category.id_comp, Category.comp_id]
  exact ιTotal_congr C K (add_zero p) (add_zero n).symm _ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The totalization shift comparison is compatible with addition of shifts. -/
theorem shiftIso_add (a b : ℤ) :
    shiftIso C (a + b) = Functor.CommShift.isoAdd (shiftIso C a) (shiftIso C b) := by
  ext K n
  simp only [Functor.CommShift.isoAdd_hom_app]
  dsimp [shiftIso, rawDirect]
  apply total.hom_ext
  intro p q h
  rw [K.ι_totalShift₁Iso_hom_f (a + b) p q n h _ rfl _ rfl, ιTotal_map_assoc,
    CochainComplex.shiftFunctorAdd_hom_app_f, CochainComplex.shiftFunctorAdd_inv_app_f,
    ι_totalShift₁Iso_hom_f_assoc _ b p q n h _ rfl _ rfl]
  dsimp [shiftFunctor₁XXIso]
  simp only [Category.id_comp, Category.comp_id]
  rw [ι_totalShift₁Iso_hom_f_assoc _ a (p + b) q (n + b)
    (by dsimp at h ⊢; lia) _ rfl _ rfl]
  dsimp [shiftFunctor₁XXIso]
  simp only [Category.id_comp]
  exact ιTotal_congr C K (by lia) (by lia) _ _

/-- The component of the raw direct totalization shift comparison is `totalShift₁Iso`. -/
@[simp]
theorem shiftIso_hom_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (shiftIso C n).hom.app K = (K.totalShift₁Iso n).hom := rfl

/-- The inverse component of the raw direct totalization shift comparison is the inverse of
`totalShift₁Iso`. -/
@[simp]
theorem shiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (shiftIso C n).inv.app K = (K.totalShift₁Iso n).inv := rfl

end rawDirect

/-- Raw direct totalization commutes with cochain shifts. -/
noncomputable instance rawDirectCommShift : (rawDirect C).CommShift ℤ where
  commShiftIso := rawDirect.shiftIso C
  commShiftIso_zero := rawDirect.shiftIso_zero C
  commShiftIso_add := rawDirect.shiftIso_add C

/-- Raw flipped totalization commutes with shifts, by transport across the total-flip
comparison. -/
noncomputable instance rawFlippedCommShift : (rawFlipped C).CommShift ℤ :=
  Functor.CommShift.ofIso (rawFlippedIsoDirect C).symm ℤ

namespace rawFlippedIsoDirect

/-- The inverse total-flip comparison is compatible with the transported shift structure. -/
noncomputable instance symmHomCommShift :
    NatTrans.CommShift (rawFlippedIsoDirect C).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility (rawFlippedIsoDirect C).symm ℤ

/-- The total-flip comparison is compatible with shifts. -/
noncomputable instance homCommShift :
    NatTrans.CommShift (rawFlippedIsoDirect C).hom ℤ :=
  NatTrans.CommShift.of_iso_inv (rawFlippedIsoDirect C).symm ℤ

end rawFlippedIsoDirect

/-- Direct totalization on homotopy categories commutes with shifts. -/
noncomputable instance directCommShift : (direct C).CommShift ℤ :=
  CategoryTheory.Functor.Homotopy.liftCommShift _ _

/-- Flipped totalization on homotopy categories commutes with shifts. -/
noncomputable instance flippedCommShift : (flipped C).CommShift ℤ :=
  CategoryTheory.Functor.Homotopy.liftCommShift _ _

namespace flippedIsoDirect

/-- The descended total-flip comparison is compatible with shifts. -/
noncomputable instance homCommShift :
    NatTrans.CommShift (flippedIsoDirect C).hom ℤ :=
  CategoryTheory.Functor.Homotopy.liftIso.homCommShift
    (rawFlipped C) (rawFlippedPreservesHomotopy C)
    (rawDirectPreservesHomotopy C) (rawFlippedIsoDirect C)

end flippedIsoDirect

namespace direct

/-- On a quotient object, the direct-totalization shift comparison is computed from the raw
comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_hom_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((direct C).commShiftIso n).hom.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (direct C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).inv.app K) ≫
        (((rawDirect C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).hom.app K) := by
  exact CategoryTheory.Quotient.LiftCommShift.iso_hom_app _ _ _ n K

/-- On a quotient object, the inverse direct-totalization shift comparison is computed from the
raw comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((direct C).commShiftIso n).inv.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (((rawDirect C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).inv.app K) ≫
        (direct C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).hom.app K) := by
  exact CategoryTheory.Quotient.LiftCommShift.iso_inv_app _ _ _ n K

end direct

namespace flipped

/-- On a quotient object, the flipped-totalization shift comparison is computed from the raw
comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_hom_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((flipped C).commShiftIso n).hom.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (flipped C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).inv.app K) ≫
        (((rawFlipped C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).hom.app K) := by
  exact CategoryTheory.Quotient.LiftCommShift.iso_hom_app _ _ _ n K

/-- On a quotient object, the inverse flipped-totalization shift comparison is computed from the
raw comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((flipped C).commShiftIso n).inv.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (((rawFlipped C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).inv.app K) ≫
        (flipped C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).hom.app K) := by
  exact CategoryTheory.Quotient.LiftCommShift.iso_inv_app _ _ _ n K

end flipped

end HomologicalComplex₂.HomotopyTotal
