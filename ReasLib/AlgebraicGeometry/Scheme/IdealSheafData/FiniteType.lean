module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

@[expose] public section

/-!
# Finite-type ideal sheaves

This file records finite type for ideal-sheaf data in terms of finite generation on affine opens.
-/

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Ideal-sheaf data is of finite type when its ideal of sections is finitely generated on every
affine open. -/
def IsFiniteType (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (I.ideal U).FG

/-- Finite type for ideal-sheaf data is equivalent to finite generation of its section ideal on
every affine open. -/
theorem isFiniteType_iff (I : X.IdealSheafData) :
    I.IsFiniteType ↔ ∀ U : X.affineOpens, (I.ideal U).FG := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
