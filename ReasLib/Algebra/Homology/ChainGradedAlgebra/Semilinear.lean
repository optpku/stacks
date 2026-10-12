/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Predifferential

/-!
# Semilinear equivalences of chain-graded algebras

A ring equivalence permits homogeneous pieces over different scalar rings to be compared by
semilinear equivalences.  This file bundles multiplicative degreewise comparisons and transports
homogeneous maps, derivations, predifferentials, and closedness by conjugation.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace ChainGradedAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Registering this constructor globally gives arbitrary ring equivalences competing inverse-pair
-- paths and can make semilinear instance search loop. This support leaf needs it only while
-- elaborating maps over one explicit `RingEquiv`; the resulting API carries no instance argument,
-- so consumers do not need another local registration.
attribute [local instance] RingHomInvPair.of_ringEquiv

/-- A multiplicative degreewise semilinear equivalence of chain-graded algebras over equivalent
scalar rings. -/
@[stacks 09PS "semilinear equivalence of chain-graded algebras"]
structure SemilinearEquiv (e : R ≃+* S) (A : ChainGradedAlgebra.{u, w} R)
    (B : ChainGradedAlgebra.{v, x} S) where
  /-- The semilinear equivalence on each homogeneous piece. -/
  map (i : ℤ) : A.X i ≃ₛₗ[RingHomClass.toRingHom e] B.X i
  /-- The degreewise equivalence preserves the homogeneous unit. -/
  map_one : map 0 A.one = B.one
  /-- The degreewise equivalence preserves homogeneous multiplication. -/
  map_mul (i j : ℤ) (a : A.X i) (b : A.X j) :
    map (i + j) (A.mul i j a b) = B.mul i j (map i a) (map j b)

namespace SemilinearEquiv

variable {e : R ≃+* S} {A : ChainGradedAlgebra.{u, w} R}
variable {B : ChainGradedAlgebra.{v, x} S}

/-- A semilinear graded-algebra equivalence acts degreewise. -/
instance instCoeFun : CoeFun (SemilinearEquiv e A B)
    (fun _ ↦ ∀ i : ℤ, A.X i → B.X i) where
  coe E := fun i x ↦ E.map i x

/-- Degreewise evaluation uses the corresponding semilinear equivalence. -/
@[simp]
theorem coe_apply (E : SemilinearEquiv e A B) (i : ℤ) (a : A.X i) :
    E i a = E.map i a := sorry

/-- Conjugation by a semilinear graded equivalence preserves addition. -/
theorem conjugateMap_add (E : SemilinearEquiv e A B) {k : ℤ}
    (D : HomogeneousMap A k) (i : ℤ) (x y : B.X i) :
    E.map (i + k) (D i ((E.map i).symm (x + y))) =
      E.map (i + k) (D i ((E.map i).symm x)) +
        E.map (i + k) (D i ((E.map i).symm y)) := sorry

/-- Conjugation by a semilinear graded equivalence preserves target scalar multiplication. -/
theorem conjugateMap_smul (E : SemilinearEquiv e A B) {k : ℤ}
    (D : HomogeneousMap A k) (i : ℤ) (r : S) (x : B.X i) :
    E.map (i + k) (D i ((E.map i).symm (r • x))) =
      r • E.map (i + k) (D i ((E.map i).symm x)) := sorry

/-- Conjugate one component of a homogeneous map by a semilinear graded equivalence. -/
def conjugateMap (E : SemilinearEquiv e A B) {k : ℤ}
    (D : HomogeneousMap A k) (i : ℤ) : B.X i →ₗ[S] B.X (i + k) where
  toFun x := E.map (i + k) (D i ((E.map i).symm x))
  map_add' := E.conjugateMap_add D i
  map_smul' := E.conjugateMap_smul D i

/-- Conjugate a homogeneous map by a semilinear graded-algebra equivalence. -/
@[stacks 09PS "transport of homogeneous maps across scalar equivalence"]
def conjugateHomogeneousMap (E : SemilinearEquiv e A B) {k : ℤ}
    (D : HomogeneousMap A k) : HomogeneousMap B k :=
  fun i ↦ E.conjugateMap D i

/-- Conjugated homogeneous maps evaluate by applying the inverse comparison, the original map,
and the forward comparison. -/
@[simp]
theorem conjugateHomogeneousMap_apply (E : SemilinearEquiv e A B) {k : ℤ}
    (D : HomogeneousMap A k) (i : ℤ) (x : B.X i) :
    E.conjugateHomogeneousMap D i x =
      E.map (i + k) (D i ((E.map i).symm x)) := sorry

/-- Conjugating a graded derivation preserves the graded Leibniz rule. -/
theorem conjugateHomogeneousMap_mem (E : SemilinearEquiv e A B) {k : ℤ}
    (D : Derivation A k) :
    E.conjugateHomogeneousMap (Derivation.toHomogeneousMap D) ∈
      derivationSubmodule B k := sorry

/-- Transport a homogeneous derivation across a semilinear graded-algebra equivalence. -/
@[stacks 09PS "transport of graded derivations across scalar equivalence"]
def conjugateDerivation (E : SemilinearEquiv e A B) {k : ℤ}
    (D : Derivation A k) : Derivation B k :=
  ⟨E.conjugateHomogeneousMap (Derivation.toHomogeneousMap D),
    E.conjugateHomogeneousMap_mem D⟩

/-- A conjugated derivation evaluates by semilinear conjugation. -/
@[simp]
theorem conjugateDerivation_apply (E : SemilinearEquiv e A B) {k : ℤ}
    (D : Derivation A k) (i : ℤ) (x : B.X i) :
    E.conjugateDerivation D i x =
      E.map (i + k) (D i ((E.map i).symm x)) := sorry

/-- Transport a predifferential across a semilinear graded-algebra equivalence. -/
def conjugatePredifferential (E : SemilinearEquiv e A B)
    (d : Predifferential A) : Predifferential B :=
  E.conjugateDerivation d

/-- Closedness of a derivation is preserved when both it and the predifferential are
conjugated. -/
theorem isClosed_conjugate (E : SemilinearEquiv e A B) {k : ℤ}
    {D : Derivation A k} {d : Predifferential A} (hD : Derivation.IsClosed D d) :
    Derivation.IsClosed (E.conjugateDerivation D)
      (E.conjugatePredifferential d) := sorry

/-- Closedness transports to any target predifferential identified with the conjugated source
predifferential. -/
theorem isClosed_conjugate_of_eq (E : SemilinearEquiv e A B) {k : ℤ}
    {D : Derivation A k} {d : Predifferential A} {d' : Predifferential B}
    (hD : Derivation.IsClosed D d) (hd : E.conjugatePredifferential d = d') :
    Derivation.IsClosed (E.conjugateDerivation D) d' := sorry

end SemilinearEquiv

end ChainGradedAlgebra
