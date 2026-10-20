/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.LinearAlgebra.Trace.Coinvariants

/-!
# Coinvariants complexes and their degree-one endomorphisms
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open scoped MonoidAlgebra

noncomputable section

universe u v w

namespace MonoidAlgebra.Coinvariants

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ]

/-- A monoid-algebra differential restricted to coefficient scalars. -/
def restrictD (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module Λ (P.X n)] [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    (n : ℕ) : P.X (n + 1) →ₗ[Λ] P.X n :=
  (P.d (n + 1) n).hom.restrictScalars Λ

variable (S : NatMonoidExtension G Γ) (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [hRestriction : ∀ n, IsRestrictionAlongInl Λ S (P.X n)]

include hRestriction in
/-- A differential followed by the coinvariant quotient is invariant under the kernel group. -/
theorem d_invariant (n : ℕ) (g : G) (p : P.X (n + 1)) :
    ((mk Λ G (P.X n)).comp (restrictD P n)) ((single g (1 : Λ) : Λ[G]) • p) =
      ((mk Λ G (P.X n)).comp (restrictD P n)) p := by
  sorry

/-- The differential induced on the coinvariants of consecutive terms. -/
def d (n : ℕ) :
    Coinvariants Λ G (P.X (n + 1)) →ₗ[Λ] Coinvariants Λ G (P.X n) :=
  lift Λ G (P.X (n + 1)) ((mk Λ G (P.X n)).comp (restrictD P n))
    (d_invariant S P n)

/-- Consecutive descended differentials compose to zero. -/
theorem d_comp_d (n : ℕ) :
    ModuleCat.ofHom (d S P (n + 1)) ≫ ModuleCat.ofHom (d S P n) = 0 := by
  sorry

/-- The chain complex obtained by taking kernel-group coinvariants in every degree. -/
def complex : ChainComplex (ModuleCat.{u} Λ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of Λ (Coinvariants Λ G (P.X n)))
    (fun n ↦ ModuleCat.ofHom (d S P n)) (d_comp_d S P)

/-- The terms of the coinvariants complex are the corresponding quotient modules. -/
theorem complex_X (n : ℕ) :
    (complex S P).X n = ModuleCat.of Λ (Coinvariants Λ G (P.X n)) := rfl

/-- The adjacent differentials of the coinvariants complex are the descended differentials. -/
theorem complex_d (n : ℕ) :
    ((complex S P).d (n + 1) n).hom = d S P n := by
  dsimp only [complex, ChainComplex.of]
  rw [ChainComplex.of_d]
  rfl

/-- The degree-one action commutes with the descended differential. -/
theorem oneEnd_comm_d (n : ℕ) :
    (d S P n).comp (oneEnd S (P.X (n + 1))) =
      (oneEnd S (P.X n)).comp (d S P n) := by
  sorry

/-- The chain endomorphism induced by the degree-one generator of the quotient monoid. -/
def oneEndChainMap : complex S P ⟶ complex S P :=
  ChainComplex.ofHom (X := complex S P) (Y := complex S P) (fun n ↦ ModuleCat.ofHom
    (X := Coinvariants Λ G (P.X n))
    (Y := Coinvariants Λ G (P.X n)) (oneEnd S (P.X n))) fun n ↦ by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, complex_d]
    exact oneEnd_comm_d S P n

end MonoidAlgebra.Coinvariants
