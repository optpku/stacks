/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Projective.Cover
import StacksCheckRecall

@[expose] public section

universe u v w

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Definition 47.4.1: A surjective linear map `f : P →ₗ[R] M` is a projective
cover, also called a projective envelope, when `P` is projective and `f` is an essential
surjection. -/
@[stacks 08XY] #check (LinearMap.IsProjectiveCover : (P →ₗ[R] M) → Prop)

/- The defining characterization of a projective cover. -/
#check (LinearMap.IsProjectiveCover.iff_projective_and_essentialSurjection :
  ∀ {f : P →ₗ[R] M},
    f.IsProjectiveCover ↔ Module.Projective R P ∧ f.IsEssentialSurjection)
