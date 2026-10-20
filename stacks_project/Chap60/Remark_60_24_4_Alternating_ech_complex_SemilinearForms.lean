/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.LinearAlgebra.ExteriorPower.Forms
public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars

@[expose] public section
universe u
namespace CrystallineSemilinearForms

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
variable (f : M →ₛₗ[algebraMap R S] N)

/-- A semilinear map regarded in the canonical restricted target module. -/
noncomputable def restricted : M →ₗ[R] RestrictScalars R S N where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smulₛₗ

/-- Exterior forms are mapped by the ring map in degree zero, by f in
degree one, and by the actual exterior-power map in all higher degrees. -/
noncomputable def map (n : ℕ) :
    exteriorPower.form R M n →ₛₗ[algebraMap R S] exteriorPower.form S N n :=
  match n with
  | 0 =>
      { toFun := algebraMap R S
        map_add' := map_add (algebraMap R S)
        map_smul' := map_mul (algebraMap R S) }
  | 1 => f
  | n + 2 =>
      { toFun := exteriorPower.RestrictScalars.map (n + 2) (restricted f)
        map_add' := map_add (exteriorPower.RestrictScalars.map (n + 2) (restricted f))
        map_smul' := (exteriorPower.RestrictScalars.map (n + 2) (restricted f)).map_smul }

/-- The degree-zero map keeps the actual scalar transport. -/
theorem map_zero (b : R) : map f 0 b = algebraMap R S b := rfl

/-- The degree-one map keeps the original map, with no dummy replacement. -/
theorem map_one (m : M) : map f 1 m = f m := rfl

end CrystallineSemilinearForms
