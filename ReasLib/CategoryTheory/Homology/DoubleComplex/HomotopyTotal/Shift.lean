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

/-- The totalization shift comparison at zero is the canonical zero-shift comparison. -/
theorem shiftIso_zero :
    shiftIso C 0 = Functor.CommShift.isoZero (rawDirect C) ℤ := sorry

/-- The totalization shift comparison is compatible with addition of shifts. -/
theorem shiftIso_add (a b : ℤ) :
    shiftIso C (a + b) = Functor.CommShift.isoAdd (shiftIso C a) (shiftIso C b) := sorry

/-- The component of the raw direct totalization shift comparison is `totalShift₁Iso`. -/
@[simp]
theorem shiftIso_hom_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (shiftIso C n).hom.app K = (K.totalShift₁Iso n).hom := sorry

/-- The inverse component of the raw direct totalization shift comparison is the inverse of
`totalShift₁Iso`. -/
@[simp]
theorem shiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (shiftIso C n).inv.app K = (K.totalShift₁Iso n).inv := sorry

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
        (((rawDirect C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).hom.app K) := sorry

/-- On a quotient object, the inverse direct-totalization shift comparison is computed from the
raw comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((direct C).commShiftIso n).inv.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (((rawDirect C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).inv.app K) ≫
        (direct C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).hom.app K) := sorry

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
        (((rawFlipped C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).hom.app K) := sorry

/-- On a quotient object, the inverse flipped-totalization shift comparison is computed from the
raw comparison and the canonical source-quotient shift comparison. -/
@[simp]
theorem commShiftIso_inv_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    ((flipped C).commShiftIso n).inv.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (((rawFlipped C ⋙ HomotopyCategory.quotient C (up ℤ)).commShiftIso n).inv.app K) ≫
        (flipped C).map
          (((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).commShiftIso n).hom.app K) := sorry

end flipped

end HomologicalComplex₂.HomotopyTotal
