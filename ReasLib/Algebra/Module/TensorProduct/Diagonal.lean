/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Diagonal group-ring action on a mixed tensor

This module equips a mixed tensor product with the diagonal group-ring action
and records its finite and projective module instances.
-/

@[expose] public section

noncomputable section

universe u v w p m

open scoped MonoidAlgebra TensorProduct

namespace TensorProduct

variable (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
variable [AddCommGroup P] [Module A P]
variable [AddCommGroup M] [Module A M]

/-- The tensor product `P ⊗[A] M`, as a type synonym for a diagonal module. -/
@[nolint unusedArguments]
def Diagonal (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M] : Type (max p m) :=
  P ⊗[A] M

namespace Diagonal

/-- The additive group structure inherited by the diagonal tensor. -/
instance instAddCommGroup : AddCommGroup (Diagonal A Λ G P M) :=
  inferInstanceAs (AddCommGroup (P ⊗[A] M))

/-- The left `A`-module structure inherited by the diagonal tensor. -/
instance instModuleA : Module A (Diagonal A Λ G P M) :=
  inferInstanceAs (Module A (P ⊗[A] M))

/-- An elementary tensor viewed in the diagonal type synonym. -/
def tmul (p : P) (m : M) : Diagonal A Λ G P M := p ⊗ₜ[A] m

/-- The canonical additive equivalence from the diagonal synonym to the raw tensor. -/
def addEquiv : Diagonal A Λ G P M ≃+ P ⊗[A] M :=
  AddEquiv.refl _

/-- The additive equivalence sends elementary tensors to elementary tensors. -/
theorem addEquiv_tmul (p : P) (m : M) :
    addEquiv A Λ G P M (tmul A Λ G P M p m) = p ⊗ₜ[A] m := sorry

end Diagonal

variable [Module Λ M] [IsScalarTower A Λ M]

set_option backward.privateInPublic true in
/-- The unit law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_one :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (1 : Λ)) =
      (1 : Module.End A (Diagonal A Λ G P M)) := sorry

set_option backward.privateInPublic true in
/-- The multiplicative law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_mul (r s : Λ) :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (r * s)) =
      map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M r) *
        map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M s) := sorry

set_option backward.privateInPublic true in
/-- The zero law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_zero :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (0 : Λ)) =
      (0 : Module.End A (Diagonal A Λ G P M)) := sorry

set_option backward.privateInPublic true in
/-- The additive law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_add (r s : Λ) :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (r + s)) =
      map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M r) +
        map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M s) := sorry

set_option backward.privateInPublic true in
/-- Left `Λ`-scaling on the second factor, as `A`-endomorphisms of the tensor. -/
def lsmulRight : Λ →+* Module.End A (Diagonal A Λ G P M) where
  toFun r := map LinearMap.id (DistribSMul.toLinearMap A M r)
  map_one' := lsmulRight_map_one A Λ G P M
  map_mul' := fun r s =>
    lsmulRight_map_mul (A := A) (Λ := Λ) (P := P) (M := M) r s
  map_zero' := lsmulRight_map_zero A Λ G P M
  map_add' := fun r s =>
    lsmulRight_map_add (A := A) (Λ := Λ) (P := P) (M := M) r s

/-- Left `Λ`-scaling acts on elementary tensors through the second factor. -/
theorem lsmulRight_tmul (r : Λ) (p : P) (m : M) :
    lsmulRight A Λ G P M r (Diagonal.tmul A Λ G P M p m) =
      Diagonal.tmul A Λ G P M p (r • m) := sorry

variable [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]

/-- The `A`-action on `M` is the restriction of the `Λ[G]`-action. -/
instance instIsScalarTower : IsScalarTower A (Λ[G]) M :=
  IsScalarTower.to₁₃₄ A Λ (Λ[G]) M

set_option backward.privateInPublic true in
/-- The unit law for the diagonal group endomorphisms. -/
private theorem diagonalOf_map_one :
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G 1))
        (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G 1)) =
      (1 : Module.End A (Diagonal A Λ G P M)) := sorry

set_option backward.privateInPublic true in
/-- The multiplicative law for the diagonal group endomorphisms. -/
private theorem diagonalOf_map_mul (g h : G) :
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G (g * h)))
        (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G (g * h))) =
      map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g))
          (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g)) *
        map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G h))
          (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G h)) := sorry

set_option backward.privateInPublic true in
/-- The diagonal `G`-action on the tensor, as `A`-endomorphisms. -/
def diagonalOf : G →* Module.End A (Diagonal A Λ G P M) where
  toFun g :=
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g))
      (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g))
  map_one' := diagonalOf_map_one A Λ G P M
  map_mul' := diagonalOf_map_mul A Λ G P M

/-- The diagonal group action sends elementary tensors to elementary tensors. -/
theorem diagonalOf_tmul (g : G) (p : P) (m : M) :
    diagonalOf A Λ G P M g (Diagonal.tmul A Λ G P M p m) =
      Diagonal.tmul A Λ G P M (MonoidAlgebra.of A G g • p)
        (MonoidAlgebra.of Λ G g • m) := sorry

set_option backward.privateInPublic true in
/-- The group-ring homomorphism encoding the diagonal `Λ[G]`-action. -/
private theorem lsmulRight_commute_diagonalOf (r : Λ) (g : G) :
    Commute (lsmulRight A Λ G P M r) (diagonalOf A Λ G P M g) := sorry

set_option backward.privateInPublic true in
/-- The group-ring map encoding the diagonal `Λ[G]`-action on the tensor. -/
def liftDiagonal : Λ[G] →+* Module.End A (Diagonal A Λ G P M) :=
  MonoidAlgebra.liftNCRingHom (lsmulRight A Λ G P M) (diagonalOf A Λ G P M)
    (lsmulRight_commute_diagonalOf A Λ G P M)

/-- On basis elements, the diagonal action is scalar multiplication after the group action. -/
theorem liftDiagonal_single (g : G) (r : Λ) :
    liftDiagonal A Λ G P M (MonoidAlgebra.single g r) =
      lsmulRight A Λ G P M r * diagonalOf A Λ G P M g := sorry

namespace Diagonal

/-- The diagonal left `Λ[G]`-module structure on the tensor. -/
instance instModule : Module (Λ[G]) (Diagonal A Λ G P M) :=
  Module.compHom (Diagonal A Λ G P M) (liftDiagonal A Λ G P M)

/-- The diagonal action on elementary tensors for an arbitrary group-ring element. -/
theorem smul_tmul (x : Λ[G]) (p : P) (m : M) :
    x • tmul A Λ G P M p m =
      x.coeff.sum fun g r ↦
        tmul A Λ G P M (MonoidAlgebra.of A G g • p)
          (r • (MonoidAlgebra.of Λ G g • m)) := sorry

/-- A group element acts diagonally on elementary tensors. -/
theorem smul_of (g : G) (p : P) (m : M) :
    MonoidAlgebra.of Λ G g • tmul A Λ G P M p m =
      tmul A Λ G P M (MonoidAlgebra.of A G g • p) (MonoidAlgebra.of Λ G g • m) :=
  sorry

/-- A basis element `r · g` acts diagonally on elementary tensors. -/
theorem smul_single (g : G) (r : Λ) (p : P) (m : M) :
    MonoidAlgebra.single g r • tmul A Λ G P M p m =
      tmul A Λ G P M (MonoidAlgebra.of A G g • p)
        (r • (MonoidAlgebra.of Λ G g • m)) := sorry

/-- The diagonal tensor is finite when `P` and `M` have the stated finiteness. -/
instance instFinite [Module.Finite (A[G]) P] [Module.Finite Λ M] :
    Module.Finite (Λ[G]) (Diagonal A Λ G P M) := sorry

/-- The diagonal tensor is projective when `P` and `M` have the stated projectivity. -/
instance instProjective [Module.Projective (A[G]) P] [Module.Projective Λ M] :
    Module.Projective (Λ[G]) (Diagonal A Λ G P M) := sorry

end Diagonal

end TensorProduct
