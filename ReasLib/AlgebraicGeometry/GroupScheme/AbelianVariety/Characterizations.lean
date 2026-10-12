/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Projective
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Smooth
public import ReasLib.AlgebraicGeometry.GroupScheme.Connected
public import ReasLib.AlgebraicGeometry.GroupScheme.GeometricallyIrreducible

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]

/-- A proper, connected, and geometrically reduced group scheme over a field is an abelian
variety. -/
instance instOfProperConnectedGeometricallyReduced
    (A : SchemeOverField k) [GrpObj A] [IsProper A.hom]
    [ConnectedSpace A.left] [GeometricallyReduced A.hom] :
    AlgebraicGeometry.AbelianVariety A := sorry

/-- A group scheme over a field is an abelian variety exactly when it is proper, connected,
and geometrically reduced over the field. -/
theorem iff_proper_connected_geometricallyReduced
    (A : SchemeOverField k) [GrpObj A] :
    AlgebraicGeometry.AbelianVariety A ↔
      IsProper A.hom ∧ ConnectedSpace A.left ∧ GeometricallyReduced A.hom := sorry

/-- A group scheme over a field is an abelian variety exactly when it is projective,
geometrically irreducible, and smooth over the field. -/
theorem iff_projective_geometricallyIrreducible_smooth
    (A : SchemeOverField k) [GrpObj A] :
    AlgebraicGeometry.AbelianVariety A ↔
      Projective A.hom ∧ GeometricallyIrreducible A.hom ∧ Smooth A.hom := sorry

/-- The canonical abelian-variety condition and all sixteen choices of projective or proper,
geometrically irreducible or irreducible or geometrically connected or connected, and smooth
or geometrically reduced are equivalent for a group scheme over a field. -/
theorem tfae (A : SchemeOverField k) [GrpObj A] :
    List.TFAE
      [ AlgebraicGeometry.AbelianVariety A
      , Projective A.hom ∧ GeometricallyIrreducible A.hom ∧ Smooth A.hom
      , Projective A.hom ∧ GeometricallyIrreducible A.hom ∧ GeometricallyReduced A.hom
      , Projective A.hom ∧ IrreducibleSpace A.left ∧ Smooth A.hom
      , Projective A.hom ∧ IrreducibleSpace A.left ∧ GeometricallyReduced A.hom
      , Projective A.hom ∧ GeometricallyConnected A.hom ∧ Smooth A.hom
      , Projective A.hom ∧ GeometricallyConnected A.hom ∧ GeometricallyReduced A.hom
      , Projective A.hom ∧ ConnectedSpace A.left ∧ Smooth A.hom
      , Projective A.hom ∧ ConnectedSpace A.left ∧ GeometricallyReduced A.hom
      , IsProper A.hom ∧ GeometricallyIrreducible A.hom ∧ Smooth A.hom
      , IsProper A.hom ∧ GeometricallyIrreducible A.hom ∧ GeometricallyReduced A.hom
      , IsProper A.hom ∧ IrreducibleSpace A.left ∧ Smooth A.hom
      , IsProper A.hom ∧ IrreducibleSpace A.left ∧ GeometricallyReduced A.hom
      , IsProper A.hom ∧ GeometricallyConnected A.hom ∧ Smooth A.hom
      , IsProper A.hom ∧ GeometricallyConnected A.hom ∧ GeometricallyReduced A.hom
      , IsProper A.hom ∧ ConnectedSpace A.left ∧ Smooth A.hom
      , IsProper A.hom ∧ ConnectedSpace A.left ∧ GeometricallyReduced A.hom
      ] := sorry

end AlgebraicGeometry.AbelianVariety
