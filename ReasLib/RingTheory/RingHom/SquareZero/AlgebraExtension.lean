/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Split
public import ReasLib.RingTheory.RingHom.SquareZero.IsoClass

/-!
# Classification of square-zero algebra extensions

The split identity-diagram solution identifies isomorphism classes of relative
square-zero extensions with the naive cotangent Ext¹ group.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom.SquareZeroExtension

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The canonical equivalence from naive cotangent Ext¹ to square-zero extension classes. -/
def algebraExtensionEquiv :
    extOneNaiveCotangent A B N ≃ IsoClass (RingHom.id A) B (zeroKernelMap A B N) :=
  isoClassEquiv (trivialSolution A B N)

/-- The classification equivalence translates by the split extension class. -/
theorem algebraExtensionEquiv_apply (ξ : extOneNaiveCotangent A B N) :
    algebraExtensionEquiv A B N ξ =
      ξ +ᵥ isoClassMk (trivialSolution A B N) := sorry

/-- The zero Ext¹ class is represented by the split extension. -/
theorem algebraExtensionEquiv_zero :
    algebraExtensionEquiv A B N 0 = isoClassMk (trivialSolution A B N) := sorry

/-- The inverse classification map subtracts the split extension class. -/
theorem algebraExtensionEquiv_symm_apply
    (p : IsoClass (RingHom.id A) B (zeroKernelMap A B N)) :
    (algebraExtensionEquiv A B N).symm p =
      p -ᵥ isoClassMk (trivialSolution A B N) := sorry

end SquareZeroExtension

end RingHom
