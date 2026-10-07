module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Basis.Nilpotent

/-!
# Bases over local rings with nilpotent maximal ideal

This leaf owns the residue-field basis criterion for a flat module.  The quotient and residue
field are kept in their canonical forms, so consumers do not need local notation or local scalar
instances to use the statement.
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Module.Basis.LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
variable {A : Type w}

/-- Lemma 10.101.1 (Stacks `051F`): for a flat module over a local ring with nilpotent maximal
ideal, a family is a basis exactly when its image in the residue-field quotient is a basis. -/
@[stacks 051F]
theorem basis_mod_maximalIdeal_iff
    (h_nil : IsNilpotent (maximalIdeal R)) (x : A → M) :
    (∃ bbar : Module.Basis A (R ⧸ maximalIdeal R)
        (M ⧸ (maximalIdeal R • (⊤ : Submodule R M))),
      ∀ a, bbar a = Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)) (x a)) ↔
      ∃ b : Module.Basis A R M, ∀ a, b a = x a := sorry

end Module.Basis.LocalRing
