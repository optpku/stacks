/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen presentations of ring direct limits

This leaf packages the maps from the stages of a commutative-ring system to the
codomain of a chosen direct-limit equivalence.  The equivalence remains an
explicit parameter: different presentations induce different maps and scalar
actions, so none of these actions is installed globally.

@stack 05N7
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

section ToLimit

variable {T : Type w} [CommRing T]
variable {I : Type u} [Preorder I]
variable (R : I → Type v) [∀ i, CommRing (R i)]
variable (rho : ∀ i j, i ≤ j → R i →+* R j)

/-- The map from a stage to the codomain of a chosen equivalence from the ring
direct limit. -/
@[stacks 05N7 "chosen direct-limit comparison"]
noncomputable def toLimitHom
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T) (i : I) : R i →+* T :=
  e.toRingHom.comp (Ring.DirectLimit.of R (fun i j h ↦ rho i j h) i)

/-- Chosen stage maps commute with every transition map. -/
@[stacks 05N7 "chosen direct-limit comparison"]
theorem toLimitHom_comp_map
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T)
    {i j : I} (h : i ≤ j) :
    (toLimitHom R rho e j).comp (rho i j h) = toLimitHom R rho e i :=
  RingHom.ext fun x => congrArg e (Ring.DirectLimit.of_f h x)

/-- A transition map and the two chosen stage maps form the expected scalar
tower over the comparison codomain. -/
@[stacks 05N7 "chosen direct-limit comparison"]
theorem toLimit_isScalarTower
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T)
    {i j : I} (h : i ≤ j) :
    letI : Algebra (R i) (R j) := (rho i j h).toAlgebra
    letI : Algebra (R i) T := (toLimitHom R rho e i).toAlgebra
    letI : Algebra (R j) T := (toLimitHom R rho e j).toAlgebra
    IsScalarTower (R i) (R j) T :=
  letI : Algebra (R i) (R j) := (rho i j h).toAlgebra
  letI : Algebra (R i) T := (toLimitHom R rho e i).toAlgebra
  letI : Algebra (R j) T := (toLimitHom R rho e j).toAlgebra
  IsScalarTower.of_algebraMap_eq' (toLimitHom_comp_map R rho e h).symm

/-- A supplied algebra action at an earlier stage that agrees with its chosen
map to the direct-limit comparison codomain extends through every later stage
to a scalar tower.  This lets applications retain a canonical ambient action
instead of rebuilding a definitionally equal local instance. -/
@[stacks 05N7 "chosen direct-limit comparison"]
theorem toLimit_isScalarTower_of_algebraMap_eq
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T)
    {i j : I} (h : i ≤ j) [Algebra (R i) T]
    (h_algebraMap : algebraMap (R i) T = toLimitHom R rho e i) :
    letI : Algebra (R i) (R j) := (rho i j h).toAlgebra
    letI : Algebra (R j) T := (toLimitHom R rho e j).toAlgebra
    IsScalarTower (R i) (R j) T := sorry

/-- A chosen stage map and the inverse-equivalence action on the direct limit
form a scalar tower. -/
@[stacks 05N7 "chosen direct-limit comparison"]
theorem toLimitHom_inverse_isScalarTower
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T) (i : I) :
    letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ rho i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra rho i
    letI : Algebra (R i) T := (toLimitHom R rho e i).toAlgebra
    letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ rho i j h)) :=
      e.symm.toRingHom.toAlgebra
    IsScalarTower (R i) T (Ring.DirectLimit R (fun i j h ↦ rho i j h)) := sorry

end ToLimit

namespace Comparison

variable {I : Type u} [Preorder I]
variable {R : I → Type v} [∀ i, CommRing (R i)]
variable (rho : ∀ i j, i ≤ j → R i →+* R j)

/-- A chosen ring equivalence from a direct limit is an algebra equivalence
after the source receives scalars through its inverse. -/
@[stacks 05N7 "chosen direct-limit comparison"]
noncomputable def algebraEquiv {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T) :
    letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ rho i j h)) :=
      e.symm.toRingHom.toAlgebra
    Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃ₐ[T] T :=
  letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ rho i j h)) :=
    e.symm.toRingHom.toAlgebra
  { toRingEquiv := e
    commutes' := sorry }

/-- The underlying function of the comparison algebra equivalence is the
chosen ring equivalence. -/
@[simp, stacks 05N7 "chosen direct-limit comparison"]
theorem algebraEquiv_apply {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T)
    (x : Ring.DirectLimit R (fun i j h ↦ rho i j h)) :
    algebraEquiv rho e x = e x := sorry

/-- The inverse of the comparison algebra equivalence is the inverse of the
chosen ring equivalence. -/
@[simp, stacks 05N7 "chosen direct-limit comparison"]
theorem algebraEquiv_symm_apply {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T) (x : T) :
    letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ rho i j h)) :=
      e.symm.toRingHom.toAlgebra
    (algebraEquiv rho e).symm x = e.symm x := sorry

end Comparison

end Ring.DirectLimit
