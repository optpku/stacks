/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible

/-!
# Residue-field criteria for geometric connectedness

The canonical residue-field algebra induced by a structure morphism to
`Spec k` gives pointwise criteria for geometric connectedness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyConnected.ResidueField

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A connected scheme over a field is geometrically connected when the relative algebraic closure of the base residue field at one point is trivial. -/
theorem of_connectedSpace_of_algebraicClosure_eq_bot
    (hX : ConnectedSpace X) (x : X)
    (hclosed :
      Scheme.Hom.ResidueField.algebraicClosureOfResidueField f x = ⊥) :
    GeometricallyConnected f := sorry

/-- A connected scheme over a field is geometrically connected when the relative algebraic
closure of the ground field in one residue field is trivial. -/
theorem of_connectedSpace_of_groundAlgebraicClosure_eq_bot
    (hX : ConnectedSpace X) (x : X)
    (hclosed : Scheme.Hom.ResidueField.algebraicClosureOfSpec f x = ⊥) :
    GeometricallyConnected f := sorry

/-- A connected scheme over a field with a rational point is geometrically connected, expressed by an isomorphism on the residue-field map. -/
theorem of_connectedSpace_of_isIsoMap
    (hX : ConnectedSpace X) (x : X) [IsIso (f.residueFieldMap x)] :
    GeometricallyConnected f := sorry

end

end GeometricallyConnected.ResidueField

end AlgebraicGeometry
