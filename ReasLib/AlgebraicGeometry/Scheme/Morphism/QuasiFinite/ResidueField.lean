/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt

/-- A scheme morphism that is quasi-finite at a point induces a finite extension of residue
fields at that point. -/
theorem moduleFinite_residueField {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hfx : f.QuasiFiniteAt x) :
    Module.Finite (S.residueField (f x)) (X.residueField x) := sorry

end AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt
