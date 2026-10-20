module

public import ReasLib.RingTheory.RingHom.SquareZero.Solution
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

/-!
# Square-zero extensions of local complete intersection algebras
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom
namespace SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (c : KernelModule π →ₗ[A] N)

/-- For a square-zero surjection `π : A' →+* A` and a local complete intersection
`A`-algebra `B`, every prescribed `A`-linear map from the kernel of `π` to a
`B`-module `N` is induced by a compatible square-zero extension of `B` by `N`. -/
@[stacks 08S6]
theorem exists_solution_of_isLocalCompleteIntersection
    [(algebraMap A B).IsLocalCompleteIntersection] :
    Nonempty (Solution (B := B) π c) := sorry

end SquareZeroExtension

end RingHom
