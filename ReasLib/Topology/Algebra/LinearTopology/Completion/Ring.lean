/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.Topology.Algebra.LinearTopology.Completion

/-!
# Ring structure on the inverse-limit completion

If `A` is a linearly topologized commutative ring, the module completion `Completion A A`
carries pointwise ring operations, making the canonical map `of` into a ring homomorphism
`coeRingHom : A →+* Completion A A`. Stage projections are likewise ring homomorphisms,
and their kernels are the closures of the extended open ideals.
-/

@[expose] public section

noncomputable section

universe u

namespace IsLinearTopology.Completion

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- One in the inverse-limit completion is the unit family of discrete quotients. -/
instance instOne : One (Completion A A) where
  one := ⟨1, fun _ _ h ↦ Submodule.factor_mk h (1 : A)⟩

/-- Pointwise multiplication of compatible families of discrete quotients. -/
instance instMul : Mul (Completion A A) where
  mul x y :=
    ⟨x.1 * y.1, fun U U' h ↦
      (map_mul (Ideal.Quotient.factor h) (x.1 U) (y.1 U)).trans
        (congrArg₂ HMul.hMul (x.2 U U' h) (y.2 U U' h))⟩

/-- Pointwise natural-number powers of compatible families of discrete quotients. -/
instance instPow : Pow (Completion A A) ℕ where
  pow x n :=
    ⟨x.1 ^ n, fun U U' h ↦
      (map_pow (Ideal.Quotient.factor h) (x.1 U) n).trans
        (congrArg (· ^ n) (x.2 U U' h))⟩

/-- Natural-number cast of compatible families of discrete quotients. -/
instance instNatCast : NatCast (Completion A A) where
  natCast n := ⟨n, fun _ _ h ↦ Submodule.factor_mk h (n : A)⟩

/-- Integer cast of compatible families of discrete quotients. -/
instance instIntCast : IntCast (Completion A A) where
  intCast n := ⟨n, fun _ _ h ↦ Submodule.factor_mk h (n : A)⟩

/-- The inverse-limit completion of a linearly topologized ring is a commutative ring
under pointwise operations. -/
instance instCommRing : CommRing (Completion A A) :=
  Subtype.val_injective.commRing (fun x : Completion A A ↦ x.1)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Addition, multiplication, and negation are continuous on the inverse-limit completion. -/
instance instIsTopologicalRing : IsTopologicalRing (Completion A A) := sorry

/-- The inverse-limit completion is linearly topologized as a module over itself. -/
instance instIsLinearTopology_self : IsLinearTopology (Completion A A) (Completion A A) :=
  sorry

/-- The canonical ring homomorphism from a linearly topologized ring to its inverse-limit
completion. -/
def coeRingHom : A →+* Completion A A where
  toFun := of
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- The canonical map `coeRingHom` is continuous. -/
theorem continuous_coeRingHom : Continuous (coeRingHom : A → Completion A A) := sorry

/-- The underlying function of `coeRingHom` is the canonical module map `of`. -/
theorem coeRingHom_eq_of (a : A) : coeRingHom a = of a := sorry

/-- Projection from the completion onto the discrete quotient ring `A ⧸ I`. -/
def πRingHom (I : Ideal A) (hI : IsOpen (I : Set A)) : Completion A A →+* A ⧸ I where
  toFun := π I hI
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- Stage projection of the canonical map `A → Completion A A` is the quotient map. -/
theorem π_coeRingHom (I : Ideal A) (hI : IsOpen (I : Set A)) (a : A) :
    πRingHom I hI (coeRingHom a) = Ideal.Quotient.mk I a := sorry

/-- The kernel of a stage projection is the closure of the corresponding extended ideal. -/
theorem ker_πRingHom (I : Ideal A) (hI : IsOpen (I : Set A)) :
    RingHom.ker (πRingHom I hI) = (Ideal.map coeRingHom I).closure := sorry

end IsLinearTopology.Completion
