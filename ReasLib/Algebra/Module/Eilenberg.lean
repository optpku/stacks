module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eilenberg absorption for infinite free modules

This leaf records Eilenberg's absorption lemma in both retract and direct-summand form, together
with its free-complement consequence for projective modules.

@stack 0GVF
@stack 0GVG
-/

@[expose] public section

universe u v w x

namespace Module.Free

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommMonoid Q] [Module R Q]
variable {F : Type x} [AddCommMonoid F] [Module R F] [Module.Free R F]

/-- Retract form of Eilenberg absorption: a retract of a non-finitely generated free module is
absorbed by that free module. -/
@[stacks 0GVF "retract form of Eilenberg absorption"]
theorem prod_equiv_self_of_retract
    (hF : ¬ Module.Finite R F) (i : P →ₗ[R] F) (s : F →ₗ[R] P)
    (hs : s.comp i = LinearMap.id) :
    Nonempty ((P × F) ≃ₗ[R] F) := sorry
-- Proof strategy: split `F` as the image of the retract `P` plus `LinearMap.ker s`, then choose
-- an infinite basis of `F` and reindex it by an infinite-cardinal absorption equivalence so one
-- additional copy of the retract is absorbed by `F`.

/-- Lemma 15.129.1 (Eilenberg's lemma): if `P × Q` is a non-finitely generated free module
`F`, then `P × F` is linearly equivalent to `F`. -/
@[stacks 0GVF "Eilenberg absorption"]
theorem prod_equiv_self_of_prod_equiv
    (hF : ¬ Module.Finite R F) (e : (P × Q) ≃ₗ[R] F) :
    Nonempty ((P × F) ≃ₗ[R] F) := sorry
-- Proof strategy: transport the first-factor inclusion and projection of `P × Q` through `e` to
-- exhibit `P` as a retract of `F`, then apply `prod_equiv_self_of_retract`.

end Module.Free

namespace Module.Projective

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

/-- Lemma 15.129.2: every projective module has a free complement whose product with the
projective module is free. -/
@[stacks 0GVG]
theorem exists_free_prod_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      Module.Free R (P × F) := sorry
-- Proof strategy: realize projective `P` as a retract of a free module, enlarge that module to an
-- infinite free stabilization, and apply Eilenberg absorption; transport the free structure back
-- along the resulting linear equivalence `P × F ≃ₗ[R] F`.

end Module.Projective
