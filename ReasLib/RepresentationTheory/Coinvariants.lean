/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Coinvariants of a module over a monoid algebra

Coinvariants are the quotient by the coefficient-ring span of the action relations.
The coefficient ring need not be commutative.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable (Λ : Type u) (G : Type v) (P : Type w)
variable [Ring Λ] [Monoid G] [AddCommGroup P]
variable [Module (Λ[G]) P] [Module Λ P]

/-- The relation submodule spanned by the differences `single g 1 • p - p`. -/
def Coinvariants.ker : Submodule Λ P :=
  Submodule.span Λ
    (Set.range fun gp : G × P ↦ (single gp.1 (1 : Λ) : Λ[G]) • gp.2 - gp.2)

/-- The coinvariants of a monoid-algebra module are the quotient by its action relations. -/
def Coinvariants : Type w :=
  P ⧸ Coinvariants.ker Λ G P

namespace Coinvariants

/-- Coinvariants inherit the additive group structure of the quotient. -/
instance instAddCommGroup : AddCommGroup (Coinvariants Λ G P) :=
  inferInstanceAs (AddCommGroup (P ⧸ ker Λ G P))

/-- Coinvariants inherit the coefficient-ring module structure of the quotient. -/
instance instModule : Module Λ (Coinvariants Λ G P) :=
  inferInstanceAs (Module Λ (P ⧸ ker Λ G P))

/-- Each difference between a monoid translate and its original vector is a relation. -/
theorem sub_mem_ker (g : G) (p : P) :
    (single g (1 : Λ) : Λ[G]) • p - p ∈ ker Λ G P := sorry

/-- The canonical coefficient-linear quotient map to coinvariants. -/
def mk : P →ₗ[Λ] Coinvariants Λ G P :=
  Submodule.mkQ (ker Λ G P)

/-- The quotient map sends a vector to its quotient class. -/
theorem mk_apply (p : P) : mk Λ G P p = Submodule.Quotient.mk p := sorry

/-- Two vectors have the same coinvariant class exactly when their difference is a relation. -/
theorem mk_eq_iff {p q : P} :
    mk Λ G P p = mk Λ G P q ↔ p - q ∈ ker Λ G P := sorry

/-- A vector has zero coinvariant class exactly when it belongs to the relation submodule. -/
theorem mk_eq_zero {p : P} : mk Λ G P p = 0 ↔ p ∈ ker Λ G P := sorry

/-- Every coinvariant class has a representative. -/
theorem mk_surjective : Function.Surjective (mk Λ G P) := sorry

/-- Monoid elements act trivially on coinvariant classes. -/
theorem mk_smul (g : G) (p : P) :
    mk Λ G P ((single g (1 : Λ) : Λ[G]) • p) = mk Λ G P p := sorry

/-- A proposition about coinvariants follows from its truth on all representatives. -/
theorem induction_on {motive : Coinvariants Λ G P → Prop} (x : Coinvariants Λ G P)
    (h : ∀ p : P, motive (mk Λ G P p)) : motive x := sorry

/-- An invariant linear map annihilates the relation submodule. -/
theorem lift_ker_le {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    ker Λ G P ≤ LinearMap.ker f := sorry

/-- An invariant coefficient-linear map descends to coinvariants. -/
def lift {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    Coinvariants Λ G P →ₗ[Λ] M :=
  Submodule.liftQ (ker Λ G P) f (lift_ker_le Λ G P f hf)

/-- Descent evaluates on a representative as the original invariant map. -/
theorem lift_mk {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) (p : P) :
    lift Λ G P f hf (mk Λ G P p) = f p := sorry

/-- Descent composed with the quotient map is the original invariant map. -/
theorem lift_comp_mk {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    (lift Λ G P f hf).comp (mk Λ G P) = f := sorry

/-- Linear maps out of coinvariants agree when their compositions with the quotient map agree. -/
theorem hom_ext {M : Type x} [AddCommGroup M] [Module Λ M]
    {f g : Coinvariants Λ G P →ₗ[Λ] M}
    (h : f.comp (mk Λ G P) = g.comp (mk Λ G P)) : f = g := sorry

/-- Coinvariants of a finite module over a finite monoid algebra are finite over the coefficient ring. -/
instance instFinite [Finite G] [IsScalarTower Λ (Λ[G]) P] [Module.Finite (Λ[G]) P] :
    Module.Finite Λ (Coinvariants Λ G P) := sorry

/-- Coinvariants of a finite projective module over a finite monoid algebra are projective. -/
instance instProjective [Finite G] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.Projective Λ (Coinvariants Λ G P) := sorry

/-- Coinvariants of a finite projective module over a finite monoid algebra are finite projective. -/
theorem finiteProjective [Finite G] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.FiniteProjective Λ (Coinvariants Λ G P) := sorry

end Coinvariants

end MonoidAlgebra
