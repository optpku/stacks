module

public import ReasLib.RingTheory.Algebra.FreeDimensional.Action

open AlgebraicGeometry CategoryTheory Opposite

/-! Compatibility checks for the ring-level action groupoid API. -/
#check (AlgebraicGeometry.FreeDimAlgebra.conjugate :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d],
    AlgebraicGeometry.glFixOne R d → AlgebraicGeometry.FreeDimAlgebra R d →
      AlgebraicGeometry.FreeDimAlgebra R d)
#check (AlgebraicGeometry.FA.toAction :
  ∀ (R : Type) [CommRing R] (d : ℕ) [NeZero d],
    AlgebraicGeometry.FreeDimAlgebra R d ⥤
      CategoryTheory.ActionCategory (AlgebraicGeometry.glFixOne R d)ᵐᵒᵖ
        (AlgebraicGeometry.FreeDimAlgebra R d))
#check (AlgebraicGeometry.FA.mapAction :
  ∀ {R S : Type} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S),
    CategoryTheory.ActionCategory (AlgebraicGeometry.glFixOne R d)ᵐᵒᵖ
        (AlgebraicGeometry.FreeDimAlgebra R d) ⥤
      CategoryTheory.ActionCategory (AlgebraicGeometry.glFixOne S d)ᵐᵒᵖ
        (AlgebraicGeometry.FreeDimAlgebra S d))
#check (AlgebraicGeometry.FA.homEquiv :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d]
    (m m' : AlgebraicGeometry.FreeDimAlgebra R d),
    (m ⟶ m') ≃ {g : AlgebraicGeometry.glFixOne R d //
      AlgebraicGeometry.FreeDimAlgebra.conjugate g m = m'})
#check (AlgebraicGeometry.FA.arrowEquiv :
  ∀ (R : Type) [CommRing R] (d : ℕ) [NeZero d],
    AlgebraicGeometry.glFixOne R d × AlgebraicGeometry.FreeDimAlgebra R d ≃
      (Σ m : AlgebraicGeometry.FreeDimAlgebra R d,
        Σ m' : AlgebraicGeometry.FreeDimAlgebra R d, m ⟶ m'))
