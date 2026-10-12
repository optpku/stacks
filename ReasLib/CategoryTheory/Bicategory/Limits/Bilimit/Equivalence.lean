/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Equivalence

/-!
# Equivalence of bilimit apices

Universal lifts between two bilimit pseudocones are inverse up to canonical invertible
`2`-morphisms. This file packages that shape-independent fact as a bicategorical equivalence
and exposes the projection and comparison API needed by downstream constructions.

The construction is independent of any presentation of the diagram shape. In particular,
shape-specific limits should specialize this API rather than construct a second equivalence
from their component maps.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {F : J ⥤ᵖ B}

/-- The identity and composition comparisons for universal lifts give a candidate unit between
the two chosen maps of a pair of bilimit pseudocones. -/
noncomputable abbrev apexEquivalence.unitIso (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    𝟙 S.pt ≅ lift S T ≫ lift T S :=
  ColaxCostructuredArrow.IsUniversal.leftEquivalence.unitIso S T

/-- The composition and identity comparisons for universal lifts give a candidate counit between
the two chosen maps of a pair of bilimit pseudocones. -/
noncomputable abbrev apexEquivalence.counitIso (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    lift T S ≫ lift S T ≅ 𝟙 T.pt :=
  ColaxCostructuredArrow.IsUniversal.leftEquivalence.counitIso S T

/-- Any two bilimit pseudocones on the same diagram have canonically equivalent apices.

The forward and inverse `1`-morphisms are the chosen universal lifts in the two directions.
The unit is `apexEquivalence.unitIso`; `Bicategory.Equivalence.mkOfAdjointifyCounit` adjusts the
candidate `apexEquivalence.counitIso` canonically so that the triangle identity belongs to the resulting
equivalence. -/
noncomputable abbrev apexEquivalence (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    S.pt ≌ T.pt :=
  ColaxCostructuredArrow.IsUniversal.leftEquivalence S T

/-- The forward morphism of the canonical equivalence between bilimit apices is the universal
lift from the first cone to the second. -/
@[simp]
theorem apexEquivalence.hom (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).hom = lift S T := sorry

/-- The inverse morphism of the canonical equivalence between bilimit apices is the universal
lift in the reverse direction. -/
@[simp]
theorem apexEquivalence.inv (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).inv = lift T S := sorry

/-- The unit of the canonical equivalence between bilimit apices is the identity/composition
comparison assembled from universal lifts. -/
@[simp]
theorem apexEquivalence.unit (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).unit = apexEquivalence.unitIso S T := sorry

/-- The counit of the canonical equivalence between bilimit apices is the canonical adjustment
of the universal-lift candidate counit. -/
@[simp]
theorem apexEquivalence.counit (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).counit =
      Bicategory.adjointifyCounit
        (apexEquivalence.unitIso S T) (apexEquivalence.counitIso S T) := sorry

/-- The comparison of the forward map of the canonical bilimit-apex equivalence is the chosen
universal comparison with the first cone. -/
noncomputable abbrev apexEquivalence.homComparisonIso (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (T.comparison S.pt).obj (apexEquivalence S T).hom ≅ S.π :=
  ColaxCostructuredArrow.IsUniversal.leftEquivalence.homComparisonIso S T

/-- The comparison of the inverse map of the canonical bilimit-apex equivalence is the chosen
universal comparison with the second cone. -/
noncomputable abbrev apexEquivalence.invComparisonIso (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (S.comparison T.pt).obj (apexEquivalence S T).inv ≅ T.π :=
  ColaxCostructuredArrow.IsUniversal.leftEquivalence.invComparisonIso S T

/-- The forward cell of the forward apex-equivalence comparison is the chosen universal
lift comparison. -/
@[simp]
theorem apexEquivalence.homComparisonIso.hom (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homComparisonIso S T).hom =
      (lift.comparisonIso S T).hom := sorry

/-- The inverse cell of the forward apex-equivalence comparison is the inverse chosen universal
lift comparison. -/
@[simp]
theorem apexEquivalence.homComparisonIso.inv (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homComparisonIso S T).inv =
      (lift.comparisonIso S T).inv := sorry

/-- The forward cell of the inverse apex-equivalence comparison is the reverse chosen universal
lift comparison. -/
@[simp]
theorem apexEquivalence.invComparisonIso.hom (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invComparisonIso S T).hom =
      (lift.comparisonIso T S).hom := sorry

/-- The inverse cell of the inverse apex-equivalence comparison is the inverse reverse chosen
universal lift comparison. -/
@[simp]
theorem apexEquivalence.invComparisonIso.inv (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invComparisonIso S T).inv =
      (lift.comparisonIso T S).inv := sorry

/-- Every equivalence-closed object property has the same truth value on the apices of any two
bilimit pseudocones on a fixed diagram. -/
theorem apexEquivalence.objectProperty_iff (S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit]
    (P : ObjectProperty B) [P.IsClosedUnderEquivalences] :
    P S.pt ↔ P T.pt := sorry

/- Data and axiom audit (mathlib 4.32):

Every non-`Prop` declaration in this file is a transparent specialization of the generic
`ColaxCostructuredArrow.IsUniversal` equivalence API. `apexEquivalence` supplies only the
pseudocone-facing name and `pt`/`π` readouts; it introduces no additional lift, adjustment,
object-preimage choice, or public existential wrapper. -/

end Bicategory.PseudoCone

end CategoryTheory
