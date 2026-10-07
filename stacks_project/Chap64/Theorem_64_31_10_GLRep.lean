module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Conjugacy and absolute irreducibility of GLₙ-valued representations

This leaf owns conjugacy of `GL n R`-valued monoid homomorphisms, the bridge into
`Representation`, and absolute irreducibility after extension of scalars to an
algebraic closure.
-/

@[expose] public section

noncomputable section

universe u v w

open Matrix

namespace Matrix.GeneralLinearGroup

/-- Two `GL n R`-valued representations of a group are conjugate when they differ by
inner automorphism of `GL n R`. -/
def IsConjugate {G : Type u} {n : Type v} {R : Type w}
    [Group G] [DecidableEq n] [Fintype n] [CommRing R]
    (ρ σ : G →* GL n R) : Prop :=
  ∃ g : GL n R, ρ = (MulAut.conj g).toMonoidHom.comp σ

/-- Conjugacy of `GL n R`-valued representations is equivalent to the existence of
`g : GL n R` with `ρ x = g * σ x * g⁻¹` for every `x`. -/
theorem IsConjugate_iff {G : Type u} {n : Type v} {R : Type w}
    [Group G] [DecidableEq n] [Fintype n] [CommRing R]
    (ρ σ : G →* GL n R) :
    IsConjugate ρ σ ↔ ∃ g : GL n R, ∀ x : G, ρ x = g * σ x * g⁻¹ := sorry

/-- The `R[G]`-representation on `n → R` attached to a `GL n R`-valued monoid homomorphism. -/
def toRepresentation {G : Type u} {n : Type v} {R : Type w}
    [Group G] [DecidableEq n] [Fintype n] [CommRing R]
    (ρ : G →* GL n R) : Representation R G (n → R) :=
  (Units.coeHom ((n → R) →ₗ[R] (n → R))).comp (toLin.toMonoidHom.comp ρ)

/-- The linear map attached to `toRepresentation ρ g` is the image of `ρ g` under `toLin`. -/
theorem toRepresentation_apply {G : Type u} {n : Type v} {R : Type w}
    [Group G] [DecidableEq n] [Fintype n] [CommRing R]
    (ρ : G →* GL n R) (g : G) :
    toRepresentation ρ g = (toLin (ρ g) : (n → R) →ₗ[R] (n → R)) := sorry

/-- A `GL n k`-valued representation is absolutely irreducible when the scalar extension
to `AlgebraicClosure k` is irreducible as a representation on `n → AlgebraicClosure k`. -/
def IsAbsolutelyIrreducible {G : Type u} {n : Type v} {k : Type w}
    [Group G] [DecidableEq n] [Fintype n] [Field k]
    (ρ : G →* GL n k) : Prop :=
  Representation.IsIrreducible
    (toRepresentation ((map (algebraMap k (AlgebraicClosure k))).comp ρ))

/-- Unfolding of absolute irreducibility as irreducibility after extension of scalars
to an algebraic closure. -/
theorem IsAbsolutelyIrreducible_iff {G : Type u} {n : Type v} {k : Type w}
    [Group G] [DecidableEq n] [Fintype n] [Field k]
    (ρ : G →* GL n k) :
    IsAbsolutelyIrreducible ρ ↔
      Representation.IsIrreducible
        (toRepresentation ((map (algebraMap k (AlgebraicClosure k))).comp ρ)) := sorry

end Matrix.GeneralLinearGroup
