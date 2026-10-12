/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The cotangent complex of a morphism of schemes, obtained from the corresponding
morphism of ringed spaces. -/
noncomputable abbrev cotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex X.Modules ℤ :=
  RingedSpace.cotangentComplex f.toShHom

end AlgebraicGeometry.Scheme.Hom
