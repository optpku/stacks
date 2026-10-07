module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

/-!
# Finite biproducts of scheme module sheaves

This module provides the scheme-facing bridge from the canonical ringed-site module
presentation to finite biproducts in `X.Modules`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Finite biproducts in `X.Modules`, transported from the ring-sheaf presentation of a scheme. -/
noncomputable instance moduleHasFiniteBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules :=
  inferInstanceAs (HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf))

end AlgebraicGeometry.Scheme

end
