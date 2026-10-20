/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

universe u v

namespace AddMonoidHom

/-- An additive homomorphism sends the `h`-torsion subgroup into the `h`-torsion subgroup. -/
theorem mapsTo_torsionBy {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (h : ℤ) :
    Set.MapsTo φ (AddSubgroup.torsionBy A h) (AddSubgroup.torsionBy B h) := sorry

/-- The additive homomorphism induced by restricting an additive map to `h`-torsion. -/
def torsionByMap {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (h : ℤ) :
    AddSubgroup.torsionBy A h →+ AddSubgroup.torsionBy B h :=
  (φ.restrict (AddSubgroup.torsionBy A h)).codRestrict
    (AddSubgroup.torsionBy B h) (fun x ↦ mapsTo_torsionBy φ h x.property)

/-- The underlying map of `torsionByMap` is the original additive homomorphism. -/
theorem torsionByMap_apply {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (h : ℤ) (x : AddSubgroup.torsionBy A h) :
    (φ.torsionByMap h x : B) = φ (x : A) := sorry

end AddMonoidHom
