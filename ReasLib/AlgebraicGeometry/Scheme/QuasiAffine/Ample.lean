/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is quasi-affine if and only if its structure sheaf is ample. -/
theorem isQuasiAffine_iff_structureSheaf_isAmple (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ Modules.isAmpleObject (SheafOfModules.unit X.ringCatSheaf) := sorry

end AlgebraicGeometry.Scheme
