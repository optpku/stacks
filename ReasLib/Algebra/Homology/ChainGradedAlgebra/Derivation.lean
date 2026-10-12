/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra

/-!
# Derivations of chain-graded algebras

This file packages degree-`k` graded derivations as a submodule of the explicit
module of homogeneous linear-map families.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra

variable (A : ChainGradedAlgebra.{u, v} R) (k : ℤ)

/-- The graded Leibniz predicate for a homogeneous linear map of degree `k`.
The sign on a degree-`i` element is `(-1)^(k * i)`. -/
@[stacks 09PR "infrastructure: the graded Leibniz predicate"]
def SatisfiesLeibniz (D : HomogeneousMap A k) : Prop :=
  ∀ i j : ℤ, ∀ a : A.X i, ∀ b : A.X j,
    D (i + j) (A.mul i j a b) =
      A.reindex (add_right_comm i k j)
          (A.mul (i + k) j (D i a) b) +
        (k * i).negOnePow •
          A.reindex (add_assoc i j k).symm
            (A.mul i (j + k) a (D j b))

namespace SatisfiesLeibniz

/-- The zero homogeneous map satisfies the graded Leibniz rule. -/
theorem zero : SatisfiesLeibniz A k (0 : HomogeneousMap A k) := sorry

/-- The sum of two maps satisfying the graded Leibniz rule again satisfies it. -/
theorem add {D E : HomogeneousMap A k} (hD : SatisfiesLeibniz A k D)
    (hE : SatisfiesLeibniz A k E) : SatisfiesLeibniz A k (D + E) := sorry

/-- A scalar multiple of a map satisfying the graded Leibniz rule again satisfies it. -/
theorem smul (r : R) {D : HomogeneousMap A k} (hD : SatisfiesLeibniz A k D) :
    SatisfiesLeibniz A k (r • D) := sorry

end SatisfiesLeibniz

/-- The `R`-submodule of degree-`k` homogeneous maps satisfying
the graded Leibniz rule. -/
@[stacks 09PR "infrastructure: the submodule of graded derivations"]
def derivationSubmodule : Submodule R (HomogeneousMap A k) where
  carrier := {D | SatisfiesLeibniz A k D}
  zero_mem' := SatisfiesLeibniz.zero A k
  add_mem' := SatisfiesLeibniz.add A k
  smul_mem' := SatisfiesLeibniz.smul A k

/-- Membership in `derivationSubmodule A k` is the graded Leibniz rule. -/
theorem mem_derivationSubmodule (D : HomogeneousMap A k) :
    D ∈ derivationSubmodule A k ↔ SatisfiesLeibniz A k D := sorry

/-- A degree-`k` graded derivation of `A`. -/
@[stacks 09PR "infrastructure: graded derivations"]
abbrev Derivation := derivationSubmodule A k

namespace Derivation

variable {A : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- The homogeneous linear-map family underlying a graded derivation. -/
def toHomogeneousMap (D : Derivation A k) : HomogeneousMap A k :=
  D.1

/-- A graded derivation acts on each homogeneous component. -/
instance instCoeFun : CoeFun (Derivation A k)
    (fun _ ↦ ∀ i : ℤ, A.X i → A.X (i + k)) where
  coe D := fun i x ↦ toHomogeneousMap D i x

/-- Evaluation of a derivation is evaluation of its underlying homogeneous map. -/
@[simp]
theorem coe_apply (D : Derivation A k) (i : ℤ) (x : A.X i) :
    D i x = toHomogeneousMap D i x := sorry

/-- A graded derivation satisfies the graded Leibniz predicate. -/
theorem satisfiesLeibniz (D : Derivation A k) :
    SatisfiesLeibniz A k (toHomogeneousMap D) := sorry

/-- The graded Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (D : Derivation A k) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    D (i + j) (A.mul i j a b) =
      A.reindex (add_right_comm i k j)
          (A.mul (i + k) j (D i a) b) +
        (k * i).negOnePow •
          A.reindex (add_assoc i j k).symm
            (A.mul i (j + k) a (D j b)) := sorry

/-- Derivations are determined by their values on homogeneous elements. -/
@[ext]
theorem ext {D E : Derivation A k}
    (h : ∀ i : ℤ, ∀ x : A.X i, D i x = E i x) : D = E := sorry

/-- The zero derivation is pointwise zero. -/
@[simp]
theorem zero_apply (i : ℤ) (x : A.X i) :
    (0 : Derivation A k) i x = 0 := sorry

/-- Addition of derivations is pointwise addition. -/
@[simp]
theorem add_apply (D E : Derivation A k) (i : ℤ) (x : A.X i) :
    (D + E) i x = D i x + E i x := sorry

/-- Scalar multiplication of derivations is pointwise scalar multiplication. -/
@[simp]
theorem smul_apply (r : R) (D : Derivation A k) (i : ℤ) (x : A.X i) :
    (r • D) i x = r • D i x := sorry

end Derivation

end ChainGradedAlgebra
