module

public import ReasLib.RepresentationTheory.Matrix

@[expose] public section

open Matrix

universe u v w

namespace Matrix.GeneralLinearGroup

/- Conjugacy of `GL n R`-valued representations. -/
#check (Matrix.GeneralLinearGroup.IsConjugate :
  ∀ {G : Type u} {n : Type v} {R : Type w} [Group G] [DecidableEq n] [Fintype n]
    [CommRing R], (G →* GL n R) → (G →* GL n R) → Prop)

/- Pointwise characterization of conjugacy. -/
#check (Matrix.GeneralLinearGroup.isConjugate_iff :
  ∀ {G : Type u} {n : Type v} {R : Type w} [Group G] [DecidableEq n] [Fintype n]
    [CommRing R] (ρ σ : G →* GL n R),
    IsConjugate ρ σ ↔ ∃ g : GL n R, ∀ x : G, ρ x = g * σ x * g⁻¹)

/- The representation on `n → R` attached to a matrix representation. -/
#check (Matrix.GeneralLinearGroup.toRepresentation :
  ∀ {G : Type u} {n : Type v} {R : Type w} [Group G] [DecidableEq n] [Fintype n]
    [CommRing R], (G →* GL n R) → Representation R G (n → R))

/- Computation of the matrix-to-representation adapter. -/
#check (Matrix.GeneralLinearGroup.toRepresentation_apply :
  ∀ {G : Type u} {n : Type v} {R : Type w} [Group G] [DecidableEq n] [Fintype n]
    [CommRing R] (ρ : G →* GL n R) (g : G),
    toRepresentation ρ g = (toLin (ρ g) : (n → R) →ₗ[R] (n → R)))

/- Absolute irreducibility after scalar extension. -/
#check (Matrix.GeneralLinearGroup.IsAbsolutelyIrreducible :
  ∀ {G : Type u} {n : Type v} {k : Type w} [Group G] [DecidableEq n] [Fintype n]
    [Field k], (G →* GL n k) → Prop)

/- Characterization of absolute irreducibility. -/
#check (Matrix.GeneralLinearGroup.isAbsolutelyIrreducible_iff :
  ∀ {G : Type u} {n : Type v} {k : Type w} [Group G] [DecidableEq n] [Fintype n]
    [Field k] (ρ : G →* GL n k),
    IsAbsolutelyIrreducible ρ ↔
      Representation.IsIrreducible
        (toRepresentation ((map (algebraMap k (AlgebraicClosure k))).comp ρ)))

end Matrix.GeneralLinearGroup
