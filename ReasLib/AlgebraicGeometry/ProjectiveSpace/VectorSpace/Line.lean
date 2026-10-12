/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

/-!
# Projective lines in projective vector spaces

A projective line in `ℙ(V)` is presented by a surjective linear map from `V` to a
two-dimensional vector space. This file constructs its projective-spectrum embedding and
records the basic properties of its underlying closed subset.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A projective line in `ℙ(V)`, represented by a two-dimensional quotient of `V`. -/
structure Line (k : Type u) [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] where
  /-- The quotient whose projectivization is the line. -/
  quotient : V →ₗ[k] (Fin 2 → k)
  /-- The quotient is onto the two-dimensional coordinate vector space. -/
  quotient_surjective : Function.Surjective quotient

namespace Line

/-- Construct a projective line from a surjective map to a two-dimensional coordinate vector
space. -/
def ofSurjective (q : V →ₗ[k] (Fin 2 → k)) (hq : Function.Surjective q) : Line k V where
  quotient := q
  quotient_surjective := hq

/-- The symmetric-algebra map induced by a linear quotient preserves the powers-of-degree-one
gradings. -/
theorem gradedMap_mem (q : V →ₗ[k] (Fin 2 → k)) {d : ℕ}
    {x : SymmetricAlgebra k V} (hx : x ∈ grading k V d) :
    SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι k (Fin 2 → k)).comp q) x ∈
      grading k (Fin 2 → k) d := sorry

/-- The graded symmetric-algebra map induced by a linear quotient. -/
def gradedMap (q : V →ₗ[k] (Fin 2 → k)) :
    grading k V →+*ᵍ grading k (Fin 2 → k) where
  toRingHom :=
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k (Fin 2 → k)).comp q)).toRingHom
  map_mem := gradedMap_mem q

/-- Surjectivity of a linear quotient makes its induced graded map eventually degreewise
surjective. -/
theorem gradedMap_eventuallySurjective (q : V →ₗ[k] (Fin 2 → k))
    (hq : Function.Surjective q) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → Function.Surjective ((gradedMap q).gradedAddHom d) := sorry

/-- The natural domain of the projective-spectrum map induced by a line quotient is all of the
projective line. -/
theorem gradedMap_domain_eq_top (ℓ : Line k V) :
    projMapDomain (gradedMap ℓ.quotient) = ⊤ := sorry

/-- The closed immersion of the projective line determined by a two-dimensional quotient. -/
def embedding (ℓ : Line k V) :
    scheme k (Fin 2 → k) ⟶ scheme k V :=
  projMapOnTarget (gradedMap ℓ.quotient) (projMapMap (gradedMap ℓ.quotient))
    (gradedMap_domain_eq_top ℓ)

/-- The projectivization of a two-dimensional quotient is a closed immersion. -/
theorem embedding_isClosedImmersion (ℓ : Line k V) :
    IsClosedImmersion ℓ.embedding := sorry

/-- The underlying set of a projective line in `ℙ(V)`. -/
def carrier (ℓ : Line k V) : Set (scheme k V) :=
  Set.range ℓ.embedding.base

/-- The carrier of a projective line is the range of its closed immersion. -/
theorem carrier_def (ℓ : Line k V) :
    ℓ.carrier = Set.range ℓ.embedding.base := sorry

/-- The carrier of a projective line is closed in `ℙ(V)`. -/
theorem isClosed_carrier (ℓ : Line k V) : IsClosed ℓ.carrier := sorry

end Line

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
