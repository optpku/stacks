/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.RingTheory.RingHom.SquareZero.Translate

/-!
# Isomorphism classes of solutions of a fixed square-zero diagram

Two solutions of a fixed square-zero deformation problem are isomorphic when a
fitting map exists for the identity connecting diagram. Their classes form a
principal homogeneous space under the naive cotangent Ext¹ group
`extOneNaiveCotangent`, via pushout translation.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open MvPolynomial

namespace RingHom.SquareZeroExtension

variable {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable {π : A' →+* A} [π.IsSquareZeroExtension]
variable {c : KernelModule π →ₗ[A] N}

/-- The identity connecting diagram comparing two solutions of the same equation. -/
def compare (S₁ S₂ : Solution (B := B) (N := N) π c) : RelativeDiagram S₁ S₂ where
  t' := id A'
  t := id A
  g := id B
  ν := AddMonoidHom.id N
  map_smul_ν := fun _b _n ↦ rfl
  comm_base := rfl
  comm_alg := rfl
  comm_kernel := sorry

/-- The identity connecting diagram has identity maps on A', A, B, and N. -/
theorem compare_spec (S₁ S₂ : Solution (B := B) (N := N) π c) :
    (compare S₁ S₂).t' = id A' ∧ (compare S₁ S₂).t = id A ∧
      (compare S₁ S₂).g = id B ∧ (compare S₁ S₂).ν = AddMonoidHom.id N := sorry

/-- The setoid identifying solutions that admit a fitting map of `compare`. -/
def isoSetoid (π : A' →+* A) [π.IsSquareZeroExtension] (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N]
    (c : KernelModule π →ₗ[A] N) [IsScalarTower A B N] :
    Setoid (Solution (B := B) (N := N) π c) where
  r S₁ S₂ := Nonempty (FittingMap (compare S₁ S₂))
  iseqv := sorry

/-- Isomorphism classes of solutions of a fixed square-zero diagram. -/
abbrev IsoClass (π : A' →+* A) [π.IsSquareZeroExtension] (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N]
    (c : KernelModule π →ₗ[A] N) [IsScalarTower A B N] :=
  Quotient (isoSetoid π B c)

/-- The isomorphism class of a given solution. -/
def isoClassMk (S : Solution (B := B) (N := N) π c) : IsoClass π B c :=
  Quotient.mk (isoSetoid π B c) S

/-- A fitting map of the identity diagram identifies isomorphism classes. -/
theorem isoClassMk_eq_of_hom {S₁ S₂ : Solution (B := B) (N := N) π c}
    (φ : FittingMap (compare S₁ S₂)) : isoClassMk S₁ = isoClassMk S₂ := sorry

/-- Difference of polynomial kernel maps, as an A-linear map on J = ker(A[B] → B). -/
def obstructionOnKer (S₁ S₂ : Solution (B := B) (N := N) π c) :
    (Generators.self A B).toExtension.ker →ₗ[A] N where
  toFun j :=
    evalPolyKerMap S₂ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j) -
      evalPolyKerMap S₁ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j)
  map_add' := sorry
  map_smul' := sorry

/-- `obstructionOnKer` is the difference of the two polynomial kernel maps. -/
theorem obstructionOnKer_apply (S₁ S₂ : Solution (B := B) (N := N) π c)
    (j : (Generators.self A B).toExtension.ker) :
    obstructionOnKer S₁ S₂ j =
      evalPolyKerMap S₂ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j) -
        evalPolyKerMap S₁ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j) := sorry

/-- The obstruction representative Hom_B(J/J², N), obtained by lifting
`evalPolyKerMap S₂ - evalPolyKerMap S₁` through J². -/
def obstructionHom (S₁ S₂ : Solution (B := B) (N := N) π c) :
    (Generators.self A B).toExtension.Cotangent →ₗ[B] N where
  toFun x := Ideal.Cotangent.lift (obstructionOnKer S₁ S₂) sorry (Cotangent.val x)
  map_add' := sorry
  map_smul' := sorry

/-- On the class of a kernel polynomial, the obstruction representative is eval₂ - eval₁. -/
theorem obstructionHom_spec (S₁ S₂ : Solution (B := B) (N := N) π c)
    (j : (Generators.self A B).toExtension.ker) :
    obstructionHom S₁ S₂ (Cotangent.mk j) =
      evalPolyKerMap S₂ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j) -
        evalPolyKerMap S₁ (liftPoly π j.1) (liftPoly_mem_evalToB_ker j) := sorry

/-- The obstruction class o(B'₁, B'₂) in Ext¹_B(NL_{B/A}, N), against the ambient
B-module structure on N. -/
def obstruction (S₁ S₂ : Solution (B := B) (N := N) π c) : extOneNaiveCotangent A B N :=
  extOneNaiveCotangent_mk A B N (obstructionHom S₁ S₂)

/-- `obstruction` is the class of `obstructionHom`. -/
theorem obstruction_spec (S₁ S₂ : Solution (B := B) (N := N) π c) :
    obstruction S₁ S₂ = extOneNaiveCotangent_mk A B N (obstructionHom S₁ S₂) := sorry

/-- The obstruction vanishes if and only if the identity diagram admits a fitting map. -/
theorem obstruction_eq_zero_iff (S₁ S₂ : Solution (B := B) (N := N) π c) :
    obstruction S₁ S₂ = 0 ↔ Nonempty (FittingMap (compare S₁ S₂)) := sorry

/-- Translating a solution by δ realizes the class of δ as an obstruction. -/
theorem obstruction_translate (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) :
    obstruction S (translate δ S) = extOneNaiveCotangent_mk A B N δ := sorry

/-- Action of a naive Ext¹ class on an isomorphism class, via `translate`. -/
def vadd (ξ : extOneNaiveCotangent A B N) (p : IsoClass π B c) : IsoClass π B c :=
  Quotient.map₂ (fun δ S ↦ translate δ S) sorry ξ p

/-- Difference of isomorphism classes, as a naive Ext¹ class. Subtraction is oriented
so that `[B'_ξ] -ᵥ [B'] = ξ` when `o(B', B'_ξ) = ξ`. -/
def vsub (p q : IsoClass π B c) : extOneNaiveCotangent A B N :=
  Quotient.lift₂ (fun S₁ S₂ ↦ obstruction S₂ S₁) sorry p q

/-- Naive Ext¹ classes act on isomorphism classes of solutions by translation. -/
instance instVAdd_isoClass : VAdd (extOneNaiveCotangent A B N) (IsoClass π B c) where
  vadd := vadd

/-- Difference of isomorphism classes of solutions is a naive Ext¹ class. -/
instance instVSub_isoClass : VSub (extOneNaiveCotangent A B N) (IsoClass π B c) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of solutions. -/
instance instAddAction_isoClass :
    AddAction (extOneNaiveCotangent A B N) (IsoClass π B c) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) :
    extOneNaiveCotangent_mk A B N δ +ᵥ isoClassMk S = isoClassMk (translate δ S) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (S₁ S₂ : Solution (B := B) (N := N) π c) :
    isoClassMk S₁ -ᵥ isoClassMk S₂ = obstruction S₂ S₁ := sorry

/-- With a chosen solution as basepoint, isomorphism classes are an additive torsor
under Ext¹_B(NL_{B/A}, N). -/
@[reducible]
def addTorsor (S0 : Solution (B := B) (N := N) π c) :
    AddTorsor (extOneNaiveCotangent A B N) (IsoClass π B c) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- A basepoint solution makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : Solution (B := B) (N := N) π c) :
    Nonempty (IsoClass π B c) := (addTorsor S0).nonempty

/-- With a chosen solution as basepoint, the isomorphism classes of solutions
are an affine copy of the naive cotangent Ext¹ group. -/
@[stacks 08S7]
def isoClassEquiv (S0 : Solution (B := B) (N := N) π c) :
    extOneNaiveCotangent A B N ≃ IsoClass π B c where
  toFun ξ := ξ +ᵥ isoClassMk S0
  invFun p := p -ᵥ isoClassMk S0
  left_inv := sorry
  right_inv := sorry

/-- The based chart sends a naive Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : Solution (B := B) (N := N) π c)
    (ξ : extOneNaiveCotangent A B N) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : Solution (B := B) (N := N) π c) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : Solution (B := B) (N := N) π c)
    (p : IsoClass π B c) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := sorry

end SquareZeroExtension

end RingHom
