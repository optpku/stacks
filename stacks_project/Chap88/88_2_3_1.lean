module

public import ReasLib.RingTheory.AdicAlgebraSystem.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

/- 88.2.3.1: given a ring map `φ : A₁ →+* A₂` and ideals `Iᵢ` with
`φ(I₁ ^ c) ⊆ I₂` for some `c ≥ 1`, there is a base-change functor
`C₁ ⥤ C₂` sending `(B n)` to
`B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
@[stacks 0AJZ] #check (AdicAlgebraSystem.baseChange :
  ∀ {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂) {c : ℕ},
    1 ≤ c → Ideal.map φ (I₁ ^ c) ≤ I₂ →
      CategoryTheory.Functor (AdicAlgebraSystem A₁ I₁) (AdicAlgebraSystem A₂ I₂))
