/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Base

/-!
# Constant systems of algebras

This leaf promotes the constant ring-system equivalence to a fixed-base
algebra equivalence.  It is separate from the general fixed-base direct-limit
API so that users who only need arbitrary algebra systems do not import this
special case.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

variable {R : Type u} [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]
variable (I : Type w) [Preorder I] [Nonempty I]

/-- The constant `A`-system with identity maps carries its canonical
`R`-algebra structure on the directed direct limit. -/
@[stacks 031N "constant direct-limit algebra"]
noncomputable instance constantAlgebra [IsDirectedOrder I] :
    Algebra R (Ring.DirectLimit (fun _ : I ↦ A)
      (fun _ _ _ ↦ (RingHom.id A : A →+* A))) :=
  Ring.DirectLimit.algebra (R := R) (S := fun _ : I ↦ A)
    (φ := fun _ _ _ ↦ AlgHom.id R A)

/-- The directed direct limit of the constant `R`-algebra system on `A` is
canonically equivalent to `A` as an `R`-algebra. -/
@[stacks 031N "constant direct-limit algebra"]
noncomputable def constantAlgEquiv [IsDirectedOrder I] :
    Ring.DirectLimit (fun _ : I ↦ A)
      (fun _ _ _ ↦ (RingHom.id A : A →+* A)) ≃ₐ[R] A :=
  AlgEquiv.ofRingEquiv (f := Ring.DirectLimit.constantEquiv A I) sorry

/-- The constant algebra direct-limit equivalence evaluates every stage
representative to its underlying element of `A`. -/
@[simp, stacks 031N "constant direct-limit algebra"]
theorem constantAlgEquiv_of [IsDirectedOrder I] (i : I) (a : A) :
    constantAlgEquiv (R := R) A I
        (Ring.DirectLimit.of (fun _ : I ↦ A)
          (fun _ _ _ ↦ (RingHom.id A : A →+* A)) i a) = a := sorry

/-- The inverse constant algebra direct-limit equivalence sends an element of
`A` to its representative in any selected stage. -/
@[stacks 031N "constant direct-limit algebra"]
theorem constantAlgEquiv_symm_of [IsDirectedOrder I] (i : I) (a : A) :
    (constantAlgEquiv (R := R) A I).symm a =
      Ring.DirectLimit.of (fun _ : I ↦ A)
        (fun _ _ _ ↦ (RingHom.id A : A →+* A)) i a := sorry

end Ring.DirectLimit
