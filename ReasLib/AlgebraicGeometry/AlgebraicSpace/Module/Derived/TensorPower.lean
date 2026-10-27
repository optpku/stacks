/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dual
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor

/-! # Integral tensor powers of derived modules on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Natural tensor powers of a derived module, starting with the degree-zero structure sheaf. -/
def tensorPowerNat (E : ModuleDerived X) : ℕ → ModuleDerived X :=
  Nat.rec (structureSheafDerived X) (fun _ acc ↦ DerivedTensor.Right.obj acc E)

/-- The zeroth natural tensor power is the degree-zero structure sheaf. -/
theorem tensorPowerNat_zero (E : ModuleDerived X) :
    tensorPowerNat E 0 = structureSheafDerived X := sorry

/-- The successor tensor power is the derived tensor product of the preceding power with
 the original module. -/
theorem tensorPowerNat_succ (E : ModuleDerived X) (n : ℕ) :
    tensorPowerNat E (n + 1) = DerivedTensor.Right.obj (tensorPowerNat E n) E := sorry

/-- Integral multiindices for a finite list, lifted to the universe of the algebraic space. -/
abbrev tensorPowerIndex (r : ℕ) : Type u :=
  ULift.{u} (Fin r → ℤ)

/-- Lowering the universe lift of an integral multiindex recovers the original function. -/
theorem tensorPowerIndex_up (r : ℕ) (n : Fin r → ℤ) :
    (ULift.up n : tensorPowerIndex r).down = n := sorry

/-- Every natural tensor power of a perfect derived module is perfect. -/
theorem isPerfect_tensorPowerNat (E : ModuleDerived X) (hE : IsPerfect E) (n : ℕ) :
    IsPerfect (tensorPowerNat E n) := sorry

/-- Integral tensor powers use natural tensor powers for nonnegative exponents and natural
 tensor powers of the derived structure-sheaf dual for negative exponents. -/
def tensorPowerInt (E : ModuleDerived X) (n : ℤ) : ModuleDerived X :=
  match n with
  | Int.ofNat k => tensorPowerNat E k
  | Int.negSucc k => tensorPowerNat (dual E) (k + 1)

/-- Tensor powers at nonnegative integral exponents agree with natural tensor powers. -/
theorem tensorPowerInt_ofNat (E : ModuleDerived X) (n : ℕ) :
    tensorPowerInt E n = tensorPowerNat E n := sorry

/-- Tensor powers at negative-successor exponents are positive powers of the derived dual. -/
theorem tensorPowerInt_negSucc (E : ModuleDerived X) (n : ℕ) :
    tensorPowerInt E (Int.negSucc n) = tensorPowerNat (dual E) (n + 1) := sorry

/-- The tensor-power family of a finite list is the ordered fold of its integral powers,
 starting with the degree-zero structure sheaf. -/
def tensorPowerFamily {r : ℕ} (E : Fin r → ModuleDerived X) :
    tensorPowerIndex r → ModuleDerived X :=
  fun n ↦
    (List.ofFn fun i : Fin r ↦ i).foldl
      (fun acc i ↦ DerivedTensor.Right.obj acc (tensorPowerInt (E i) (n.down i)))
      (structureSheafDerived X)

/-- Evaluation of a tensor-power family at a lifted multiindex is the ordered tensor fold
 of the corresponding integral powers. -/
theorem tensorPowerFamily_apply {r : ℕ} (E : Fin r → ModuleDerived X) (n : Fin r → ℤ) :
    tensorPowerFamily E (ULift.up n) =
      (List.ofFn fun i : Fin r ↦ i).foldl
        (fun acc i ↦ DerivedTensor.Right.obj acc (tensorPowerInt (E i) (n i)))
        (structureSheafDerived X) := sorry

/-- Every integral tensor power of a perfect derived module is perfect. -/
theorem isPerfect_tensorPowerInt (E : ModuleDerived X) (hE : IsPerfect E) (n : ℤ) :
    IsPerfect (tensorPowerInt E n) := sorry

/-- The tensor-power family of a finite list of perfect derived modules is pointwise perfect. -/
theorem isPerfect_tensorPowerFamily {r : ℕ} (E : Fin r → ModuleDerived X)
    (hE : ∀ i, IsPerfect (E i)) (n : tensorPowerIndex r) :
    IsPerfect (tensorPowerFamily E n) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
