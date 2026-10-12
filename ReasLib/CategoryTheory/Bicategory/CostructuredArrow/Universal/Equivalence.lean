/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift.Functoriality

/-!
# Equivalence of universal costructured-arrow sources

Two universal objects of the same colax costructured-arrow bicategory have equivalent source
objects. The equivalence is assembled from the selected universal lifts and their identity and
composition comparisons. This is the generic owner behind equivalences of bilimit apices and
other shape-specific universal objects.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow.IsUniversal

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : A ⥤ᵖ C} {X : C}

/-- The identity and composition comparisons for universal lifts give a candidate unit between
the two selected source maps. -/
noncomputable def leftEquivalence.unitIso (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    𝟙 S.left ≅ lift S T ≫ lift T S :=
  lift.id.iso S ≪≫ (lift.comp.iso S T S).symm

/-- The composition and identity comparisons for universal lifts give a candidate counit
between the two selected source maps. -/
noncomputable def leftEquivalence.counitIso (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    lift T S ≫ lift S T ≅ 𝟙 T.left :=
  lift.comp.iso T S T ≪≫ (lift.id.iso T).symm

/-- The source objects of two universal costructured arrows are canonically equivalent through
the selected lifts in both directions. -/
noncomputable def leftEquivalence (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    S.left ≌ T.left :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (leftEquivalence.unitIso S T) (leftEquivalence.counitIso S T)

namespace leftEquivalence

/-- The forward morphism of `leftEquivalence` is the selected universal lift from `S` to `T`. -/
@[simp]
theorem hom (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence S T).hom = lift S T := sorry

/-- The inverse morphism of `leftEquivalence` is the selected universal lift from `T` to `S`. -/
@[simp]
theorem inv (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence S T).inv = lift T S := sorry

/-- The unit of `leftEquivalence` is the comparison assembled from universal lifts. -/
@[simp]
theorem unit (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence S T).unit = leftEquivalence.unitIso S T := sorry

/-- The counit of `leftEquivalence` is the canonical adjustment of the universal-lift candidate
counit. -/
@[simp]
theorem counit (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence S T).counit =
      Bicategory.adjointifyCounit
        (leftEquivalence.unitIso S T) (leftEquivalence.counitIso S T) := sorry

/-- Comparing the forward map of `leftEquivalence` recovers the structural map of `S`. -/
noncomputable def homComparisonIso (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    (T.comparison S.left).obj (leftEquivalence S T).hom ≅ S.hom :=
  lift.comparisonIso S T

namespace homComparisonIso

/-- The forward cell of the forward comparison is the selected lift comparison. -/
@[simp]
theorem hom (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence.homComparisonIso S T).hom = (lift.comparisonIso S T).hom := sorry

/-- The inverse cell of the forward comparison is the inverse selected lift comparison. -/
@[simp]
theorem inv (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence.homComparisonIso S T).inv = (lift.comparisonIso S T).inv := sorry

end homComparisonIso

/-- Comparing the inverse map of `leftEquivalence` recovers the structural map of `T`. -/
noncomputable def invComparisonIso (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    (S.comparison T.left).obj (leftEquivalence S T).inv ≅ T.hom :=
  lift.comparisonIso T S

namespace invComparisonIso

/-- The forward cell of the reverse comparison is the reverse selected lift comparison. -/
@[simp]
theorem hom (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence.invComparisonIso S T).hom = (lift.comparisonIso T S).hom := sorry

/-- The inverse cell of the reverse comparison is the inverse reverse selected lift
comparison. -/
@[simp]
theorem inv (S T : ColaxCostructuredArrow K X) [S.IsUniversal] [T.IsUniversal] :
    (leftEquivalence.invComparisonIso S T).inv = (lift.comparisonIso T S).inv := sorry

end invComparisonIso

end leftEquivalence

/-- An equivalence-closed object property has the same truth value on the source objects of two
universal costructured arrows. -/
theorem leftEquivalence.objectProperty_iff (S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal]
    (P : ObjectProperty A) [P.IsClosedUnderEquivalences] :
    P S.left ↔ P T.left := sorry

end Bicategory.ColaxCostructuredArrow.IsUniversal

end CategoryTheory
