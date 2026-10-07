module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Source comparison for fixed-right derived tensoring

The fixed-right derived tensor owner is defined from a chosen cochain representative and a
homotopy-category totalization.  This file records the canonical comparison with right tensoring
in the monoidal homotopy category.  It is deliberately separate from the derived model owner:
the comparison needs the monoidal localization data, while the model only needs a selected
left-derived universal property.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ K L : CochainComplex C ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]

/-- The totalized tensor bifunctor valued in the monoidal localization presenting the homotopy
category.  Naming this owner keeps fixed-factor lifting constructions independent of the concrete
presentation of `Localization.Monoidal.toMonoidalCategory`. -/
@[stacks 0G6E "localized tensor bifunctor"]
noncomputable abbrev localizedTensor :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤
      LocalizedMonoidal (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ))
        (HomotopyCategory.Koszul.quotientUnitIso (C := C)) :=
  curriedTensor (CochainComplex C ℤ) ⋙
    (Functor.whiskeringRight (CochainComplex C ℤ) (CochainComplex C ℤ)
      (LocalizedMonoidal (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ))
        (HomotopyCategory.Koszul.quotientUnitIso (C := C)))).obj
      (Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ))
        (HomotopyCategory.Koszul.quotientUnitIso (C := C)))

/-- The canonical localization lifting datum for the opaque fixed-right homotopy totalization.
The generic `Functor.Homotopy.liftLifting` owner cannot be recovered by reducible typeclass
search through the named `rightFixed` definition, so this specialized instance exposes its
factorization explicitly. -/
@[implicit_reducible, stacks 0G6E "fixed-right localization lifting"]
noncomputable def rightFixedLifting (P : CochainComplex C ℤ) :
    Localization.Lifting
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ))
      (MonoidalCategory.tensorRight P ⋙
        (HomotopyCategory.quotient C (up ℤ)))
      (Functor.Homotopy.BifunctorTotal.rightFixed (curriedTensor C) P) where
  iso := Functor.Homotopy.BifunctorTotal.rightFixedFactors (curriedTensor C) P

/-- The canonical localization lifting datum for right tensoring by a complex.  It is constructed
from the two-variable localized tensor, which keeps the monoidal comparison independent of the
opaque `HomotopyCategory.Koszul.monoidalCategory` instance. -/
@[implicit_reducible, stacks 0G6E "fixed-right tensor lifting"]
noncomputable def rightTensorLifting (P : CochainComplex C ℤ) :
    Localization.Lifting
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ))
      (MonoidalCategory.tensorRight P ⋙
        (HomotopyCategory.quotient C (up ℤ)))
      (MonoidalCategory.tensorRight
        ((HomotopyCategory.quotient C (up ℤ)).obj P)) where
  iso :=
    (Localization.Lifting₂.liftingLift₂Flip
      (localizedTensor (C := C))
      (hF := Localization.Monoidal.isInvertedBy₂
        (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ))
        (HomotopyCategory.Koszul.quotientUnitIso (C := C)))
      (HomotopyCategory.quotient C (up ℤ))
      (HomotopyCategory.quotient C (up ℤ)) P).iso

/-- The canonical comparison from right tensoring on the homotopy category to the descended
fixed-right totalization. -/
@[stacks 064M "fixed-right homotopy source comparison"]
noncomputable def rightFixedIso (P : CochainComplex C ℤ) :
    MonoidalCategory.tensorRight
        ((HomotopyCategory.quotient C (up ℤ)).obj P) ≅
      Functor.Homotopy.BifunctorTotal.rightFixed (curriedTensor C) P :=
  Localization.liftNatIso
    (HomotopyCategory.quotient C (up ℤ))
    (HomologicalComplex.homotopyEquivalences C (up ℤ))
    (MonoidalCategory.tensorRight P ⋙
      (HomotopyCategory.quotient C (up ℤ)))
    (MonoidalCategory.tensorRight P ⋙
      (HomotopyCategory.quotient C (up ℤ)))
    (MonoidalCategory.tensorRight
      ((HomotopyCategory.quotient C (up ℤ)).obj P))
    (Functor.Homotopy.BifunctorTotal.rightFixed (curriedTensor C) P)
    (h₁ := rightTensorLifting P)
    (h₂ := rightFixedLifting P)
    (Iso.refl _)

/-- After applying the derived-category quotient, the homotopy source comparison agrees with the
fixed-right source functor used by `DerivedTensor.Right`. -/
@[stacks 064M "fixed-right complex source comparison"]
noncomputable def sourceFunctorOfComplexIso (P : CochainComplex C ℤ) :
    MonoidalCategory.tensorRight
        ((HomotopyCategory.quotient C (up ℤ)).obj P) ⋙
        (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ≅
      DerivedTensor.Right.sourceFunctorOfComplex P :=
  Functor.isoWhiskerRight (rightFixedIso P)
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- For a derived object, right tensoring by its chosen homotopy representative has the same
source functor as the canonical fixed-right derived tensor construction. -/
@[stacks 064M "fixed-right derived source comparison"]
noncomputable def sourceFunctorIso (E : DerivedCategory C) :
    MonoidalCategory.tensorRight
        ((HomotopyCategory.quotient C (up ℤ)).obj
          ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)) ⋙
        (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ≅
      DerivedTensor.Right.sourceFunctor E :=
  sourceFunctorOfComplexIso
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)

end CategoryTheory.DerivedCategory.DerivedTensor.Right
