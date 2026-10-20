module

public import ReasLib.RingTheory.RingHom.SquareZero.CompleteIntersection
import StacksCheckRecall

/-!
# Existence of square-zero solutions for local complete intersection maps

If the structure map A → B is a local complete intersection, the standing
square-zero diagram 91.2.0.1 admits a solution.
-/

@[expose] public section

universe u

/- Lemma 91.2.9 If the structure map A → B is a local complete intersection,
then every standing square-zero diagram admits a solution. -/
@[stacks 08S6] #check
  (RingHom.SquareZeroExtension.exists_solution_of_isLocalCompleteIntersection :
    ∀ {A' A : Type u} [CommRing A'] [CommRing A]
      (π : A' →+* A) [π.IsSquareZeroExtension]
      (B : Type u) [CommRing B] [Algebra A B]
      {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      (c : RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N)
      [(algebraMap A B).IsLocalCompleteIntersection],
      Nonempty (RingHom.SquareZeroExtension.Solution (B := B) π c))
