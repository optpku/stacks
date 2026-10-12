/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Split Finite Projective Modules

This leaf records closure of finite projectivity under explicit linear
retracts at the semiring level.
-/

@[expose] public section

universe u v w

namespace Module.FiniteProjective

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {P : Type w} [AddCommMonoid P] [Module R P]

/-- Tag `00JH`: a linear retract of a finite projective module is finite projective. -/
@[stacks 00JH "finite projective modules are closed under linear retracts"]
theorem of_split (hM : Module.FiniteProjective R M)
    (i : P →ₗ[R] M) (r : M →ₗ[R] P) (hri : r.comp i = LinearMap.id) :
    Module.FiniteProjective R P := by
  letI := hM.finite
  letI := hM.projective
  have hleft : Function.LeftInverse r i := fun x ↦ DFunLike.congr_fun hri x
  exact ⟨Module.Finite.of_surjective r hleft.surjective,
    Module.Projective.of_split i r hri⟩

end Module.FiniteProjective
