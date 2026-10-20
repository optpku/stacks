/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.128.4

@stack 046Y

The local flatness criterion is recorded with the source assumptions and conclusion.  The
residue-field tensor formulation is a small quotient-map bridge; direct-limit approximation data
and its transport proof are deliberately left to the proof stage rather than exposed as chapter
API.
-/

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- A residue-field tensor injection is the same as injectivity of the corresponding closed-fiber
quotient map.  This is the canonical bridge used by the two source views of Lemma 10.128.4. -/
theorem injective_mod_maximalIdeal_of_lTensor_residueField_injective
    (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := sorry

/-- Lemma 10.128.4: for a local homomorphism `R → S` with `S` essentially of finite presentation
over `R`, finitely presented `S`-modules `M` and `N`, and `N` flat over `R`, injectivity on the
closed-fiber quotient implies that `u` is injective and `N ⧸ LinearMap.range u` is flat over `R`. -/
@[stacks 046Y]
theorem injective_and_flat_quotient_of_mod_maximalIdeal_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := sorry

/-- Residue-field version of Lemma 10.128.4, obtained by the preceding closed-fiber bridge. -/
theorem injective_and_flat_quotient_of_lTensor_residueField_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := sorry

end

#check @LinearMap.quotientMapByIdeal
#check @LinearMap.quotientMapByIdeal_injective_iff_lTensor_injective
#check @RingHom.EssFinitePresentation
#check @Module.Flat
#check @injective_and_flat_quotient_of_mod_maximalIdeal_injective
