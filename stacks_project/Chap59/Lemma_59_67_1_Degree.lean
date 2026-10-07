module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteEtaleDegree

/-!
# Finite étale morphisms of constant degree prime to ℓ

A finite étale morphism has constant degree prime to `ℓ` when its pushforward
structure sheaf is finite locally free of some rank coprime to `ℓ`.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Constant degree prime to `ℓ` is the canonical finite-locally-free rank predicate. -/
#check (AlgebraicGeometry.Scheme.FiniteEtale.IsConstantDegreePrimeTo :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → ℕ → Prop)

/- The degree predicate is characterized by a rank coprime to `ℓ`. -/
#check (AlgebraicGeometry.Scheme.FiniteEtale.isConstantDegreePrimeTo_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℓ : ℕ),
    IsConstantDegreePrimeTo f ℓ ↔
      ∃ d : ℕ, Nat.Coprime d ℓ ∧ IsFiniteLocallyFreeOfRank f d)

end AlgebraicGeometry.Scheme.FiniteEtale

end
