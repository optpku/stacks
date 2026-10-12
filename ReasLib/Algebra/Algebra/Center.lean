/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Centers of Algebras

This leaf exposes the canonical identification of a commutative algebra with its center and
the resulting transport of algebra equivalences through centers.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Subalgebra

variable (R : Type u) [CommRing R]

/-- A commutative `R`-algebra is canonically equivalent to its center. -/
def centerEquiv (A : Type v) [CommRing A] [Algebra R A] :
    center R A ≃ₐ[R] A :=
  (equivOfEq (center R A) ⊤ (center_eq_top R A)).trans topEquiv

/-- An equivalence between the centers of two commutative algebras induces an equivalence
between the algebras themselves. -/
def algEquivOfCenterAlgEquiv
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : center R A ≃ₐ[R] center R B) : A ≃ₐ[R] B :=
  (centerEquiv R A).symm.trans (e.trans (centerEquiv R B))

/-- For commutative algebras, existence of an algebra equivalence is equivalent to existence
of an equivalence between their centers. -/
theorem nonempty_algEquiv_iff_centerAlgEquiv
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    Nonempty (A ≃ₐ[R] B) ↔ Nonempty (center R A ≃ₐ[R] center R B) := sorry

end Subalgebra
