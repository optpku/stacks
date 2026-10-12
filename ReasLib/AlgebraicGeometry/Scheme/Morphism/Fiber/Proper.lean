/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Properness of a scheme morphism is inherited by its fibre over a residue field. -/
def fiberToSpecResidueField_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsProper
      ((Over.mk (f.fiberToSpecResidueField y) :
        Over (Spec (CommRingCat.of (Y.residueField y)))).hom) := sorry

end AlgebraicGeometry.Scheme.Hom
