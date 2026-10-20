module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Finite residue-field extensions give finite morphisms into decent spaces

On a decent algebraic space, a field-valued point over a closed point of the
base with finite residue-field extension is a finite morphism; it is a closed
immersion when the canonical residue-field map is bijective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued point of a decent algebraic space over a scheme is a finite
morphism if its image in the base is closed and its canonical residue-field
extension is finite. -/
theorem isFinite_of_finite_residueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (p : FieldValuedPoint X)
    (hs : closedPointImage p.structureHom ∈ closedPoints S)
    (hfin : Module.Finite (S.residueField (closedPointImage p.structureHom)) p.K) :
    IsFinite p.hom :=
  sorry

/-- A field-valued point of a decent algebraic space over a scheme is a closed
immersion if its image in the base is closed and its canonical residue-field
map is bijective. -/
theorem isClosedImmersion_of_eq_residueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (p : FieldValuedPoint X)
    (hs : closedPointImage p.structureHom ∈ closedPoints S)
    (heq : Function.Bijective
      (algebraMap (S.residueField (closedPointImage p.structureHom)) p.K)) :
    IsClosedImmersion p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
