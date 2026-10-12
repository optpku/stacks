/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.LinearAlgebra.LinearMap.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective lifting through linear-map pullbacks

This file combines the universal property of `LinearMap.pullback` with the projective lifting
property. It packages the common operation of choosing one lift which satisfies two compatible
linear equations simultaneously.

@stack 0H7M
-/

@[expose] public section

universe u v w x y z

namespace LinearMap.Pullback

variable {R : Type u} [Semiring R]
variable {L : Type v} [AddCommMonoid L] [Module R L]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type x} [AddCommMonoid N] [Module R N]
variable {P : Type y} [AddCommMonoid P] [Module R P]
variable {Q : Type z} [AddCommMonoid Q] [Module R Q] [Module.Projective R Q]

/-- A projective module lifts through a jointly surjective compatible pair of linear maps. -/
@[stacks 0H7M "projective lifting through a linear-map pullback"]
theorem exists_lift_of_surjective
    (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (a : L →ₗ[R] M) (b : L →ₗ[R] N) (hab : f.comp a = g.comp b)
    (hqab : Function.Surjective (lift f g a b hab))
    (u : Q →ₗ[R] M) (v : Q →ₗ[R] N) (huv : f.comp u = g.comp v) :
    ∃ l : Q →ₗ[R] L, a.comp l = u ∧ b.comp l = v := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property
    (lift f g a b hab) (lift f g u v huv) hqab
  refine ⟨l, ?_, ?_⟩
  · ext q
    exact congrArg (fun p : LinearMap.pullback f g => (p : M × N).1)
      (LinearMap.congr_fun hl q)
  · ext q
    exact congrArg (fun p : LinearMap.pullback f g => (p : M × N).2)
      (LinearMap.congr_fun hl q)

variable [Module.Projective R N]

/-- A jointly surjective compatible pair admits a lift which is a right inverse in the second
coordinate and realizes a prescribed compatible map in the first coordinate. -/
@[stacks 0H7M "compatible projective right inverse"]
theorem exists_compatible_rightInverse
    (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (a : L →ₗ[R] M) (b : L →ₗ[R] N) (hab : f.comp a = g.comp b)
    (hqab : Function.Surjective (lift f g a b hab))
    (u : N →ₗ[R] M) (hu : f.comp u = g) :
    ∃ l : N →ₗ[R] L, a.comp l = u ∧ b.comp l = LinearMap.id :=
  exists_lift_of_surjective f g a b hab hqab u LinearMap.id (by simpa using hu)

end LinearMap.Pullback
