module

public import Mathlib.Algebra.Field.Rat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre

/-!
# Failure of decency for the quotient of the affine line by integer translation

The quotient of the affine line over a field by integer translation carries a canonical
map from the spectrum of the residue field at the generic point of the affine line. The
point class represented by this map admits no representative that is a monomorphism from
the spectrum of a field, so the quotient over the rationals is not decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/-- The canonical image in the quotient of the affine line by integer translation of the
spectrum of the residue field at the generic point of the affine line: the generic-point
map into the affine line followed by the quotient atlas. -/
def genericToSpace (k : Type u) [Field k] [CharZero k] :
    ofOver (AffineLineTranslation.genericOver k) ⟶ space k :=
  ofOverMap (AffineLineTranslation.genericToCover k) ≫
    (atlas k : yoneda.obj (cover k) ⟶ (space k).functorOfPoints)

/-- The generic-point map into the quotient is the composite of the generic-point map into
the affine line with the quotient atlas. -/
theorem genericToSpace_eq (k : Type u) [Field k] [CharZero k] :
    genericToSpace k =
      ofOverMap (AffineLineTranslation.genericToCover k) ≫
        (atlas k : yoneda.obj (cover k) ⟶ (space k).functorOfPoints) := rfl

/-- The field-valued point of the quotient of the affine line by integer translation
represented by the canonical image of the generic residue-field spectrum. -/
def genericFieldValuedPoint (k : Type u) [Field k] [CharZero k] :
    FieldValuedPoint (space k) :=
  FieldValuedPoint.of (AffineLineTranslation.genericResidueField k)
    (AffineLineTranslation.genericStructure k) (genericToSpace k)

/-- The morphism of the generic residue-field representative into the quotient of the
affine line by integer translation is the canonical generic-point map. -/
theorem genericFieldValuedPoint_hom (k : Type u) [Field k] [CharZero k] :
    (genericFieldValuedPoint k).hom = genericToSpace k := rfl

/-- The point of the quotient of the affine line by integer translation represented by the
canonical image of the generic residue-field spectrum. -/
def genericSpacePoint (k : Type u) [Field k] [CharZero k] : Points (space k) :=
  Points.mk (genericFieldValuedPoint k)

/-- The generic point of the quotient of the affine line by integer translation is the
class of the canonical generic residue-field representative. -/
theorem mk_genericFieldValuedPoint (k : Type u) [Field k] [CharZero k] :
    genericSpacePoint k = Points.mk (genericFieldValuedPoint k) := rfl

/-- The point class represented by the canonical image of the generic residue-field
spectrum in the quotient of the affine line over the rationals by integer translation
admits no representative that is a monomorphism from the spectrum of a field. -/
theorem not_existsMono_genericPoint :
    ¬ existsMonoFieldValuedPoint (space ℚ) (genericSpacePoint ℚ) := by
  sorry

/-- The quotient of the affine line over the rationals by integer translation is not
decent: its generic point class has no monomorphic field-spectrum representative. -/
theorem not_isDecent :
    ¬ IsDecent (space ℚ) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
