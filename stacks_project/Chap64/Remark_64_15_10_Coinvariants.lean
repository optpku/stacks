/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import stacks_project.Chap64.Lemma_64_15_9_Coinvariants
public import stacks_project.Chap64.Lemma_64_15_9_Extension

/-!
# Termwise coinvariants of a complex of group-ring modules

This leaf owns the chain complex `(P_•)_G` obtained by taking coinvariants of
each term of a complex of `Λ[Γ]`-modules, restricted along a monoid extension
`S : NatMonoidExtension G Γ`.
-/

@[expose] public section

open scoped MonoidAlgebra
open HomologicalComplex

noncomputable section

universe u v w

namespace MonoidAlgebra.Coinvariants

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ]

/-- The underlying `Λ`-linear map of a differential of a complex of `Λ[Γ]`-modules. -/
def restrictD (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module Λ (P.X n)] [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    (n : ℕ) : P.X (n + 1) →ₗ[Λ] P.X n where
  toFun p := ModuleCat.Hom.hom (P.d (n + 1) n) p
  map_add' := sorry
  map_smul' := sorry

/-- The differential of the coinvariants complex in degree `n`, obtained by
descending `P.d (n + 1) n` along `Coinvariants.mk`. -/
def d (S : NatMonoidExtension G Γ) (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
    [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
    (n : ℕ) :
    Coinvariants Λ G (P.X (n + 1)) →ₗ[Λ] Coinvariants Λ G (P.X n) :=
  lift Λ G (P.X (n + 1))
    ((mk Λ G (P.X n)).comp (restrictD P n)) fun _ _ ↦ sorry

/-- The chain complex `(P_•)_G` of coinvariants of a complex of `Λ[Γ]`-modules
that are `Λ[G]`-modules by restriction along `S.inl`. -/
def complex (S : NatMonoidExtension G Γ) (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
    [∀ n, IsRestrictionAlongInl Λ S (P.X n)] :
    ChainComplex (ModuleCat.{u} Λ) ℕ :=
  ChainComplex.of
    (fun n ↦ ModuleCat.of Λ (Coinvariants Λ G (P.X n)))
    (fun n ↦ ModuleCat.ofHom (d S P n))
    fun _ ↦ sorry

/-- Objects of the coinvariants complex are the coinvariants of the terms of `P`. -/
theorem complex_X (S : NatMonoidExtension G Γ)
    (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
    [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
    (n : ℕ) :
    (complex S P).X n = ModuleCat.of Λ (Coinvariants Λ G (P.X n)) :=
  sorry

/-- Differentials of the coinvariants complex are the descended maps `d`. -/
theorem complex_d (S : NatMonoidExtension G Γ)
    (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
    [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
    [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
    [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
    (n : ℕ) :
    ModuleCat.Hom.hom ((complex S P).d (n + 1) n) = d S P n :=
  sorry

end MonoidAlgebra.Coinvariants
