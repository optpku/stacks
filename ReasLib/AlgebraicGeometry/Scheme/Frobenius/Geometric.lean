module

public import Mathlib.Data.Fintype.Card
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Iteration
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Geometric Frobenius of schemes over finite fields

This leaf owns the geometric Frobenius endomorphism π_X of a scheme over a
finite field, as the finite-field iterate of absolute Frobenius, together with
its packaging as a morphism over Spec(k).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopCat Scheme
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)

/-- The characteristic-`p` Frobenius iterate of a scheme `X` is the `f`-fold
absolute Frobenius F_X^f; over a finite field, this is geometric Frobenius. -/
def geometricFrobenius (X : SchemeOverField k) : X.left ⟶ X.left :=
  Hom.absoluteFrobeniusPowSource (p := p) X.hom f

/-- The geometric Frobenius of `X` is the `f`-fold absolute Frobenius of the
underlying scheme. -/
theorem geometricFrobenius_eq_absoluteFrobeniusPow (X : SchemeOverField k) :
    geometricFrobenius p f X =
      Hom.absoluteFrobeniusPowSource (p := p) X.hom f := sorry

/-- If `k` has `p ^ f` elements, then π_X is a morphism over Spec(k). -/
theorem geometricFrobenius_comp_hom [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : SchemeOverField k) :
    geometricFrobenius p f X ≫ X.hom = X.hom := sorry

/-- The geometric Frobenius of `X`, bundled as an endomorphism over Spec(k). -/
def geometricFrobeniusOver [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : SchemeOverField k) : X ⟶ X :=
  Over.homMk (geometricFrobenius p f X) (geometricFrobenius_comp_hom p f hcard X)

/-- The underlying scheme morphism of the bundled geometric Frobenius is π_X. -/
theorem geometricFrobeniusOver_left [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : SchemeOverField k) :
    (geometricFrobeniusOver p f hcard X).left = geometricFrobenius p f X := sorry

/-- The geometric Frobenius equals F_X^f and, when `k` has `p ^ f` elements, is a
morphism over Spec(k). -/
theorem geometricFrobenius_spec [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : SchemeOverField k) :
    geometricFrobenius p f X =
        Hom.absoluteFrobeniusPowSource (p := p) X.hom f ∧
      geometricFrobenius p f X ≫ X.hom = X.hom := sorry

/-- Geometric Frobenius is the identity on spaces, so it pulls every open back
into itself. -/
theorem geometricFrobenius_le_preimage (X : SchemeOverField k) (U : X.left.Opens) :
    U ≤ geometricFrobenius p f X ⁻¹ᵁ U := sorry

/-- On sections over an open `U`, geometric Frobenius acts by `s ↦ s ^ p ^ f`. -/
theorem geometricFrobenius_appLE (X : SchemeOverField k) (U : X.left.Opens)
    (s : Γ(X.left, U)) :
    CommRingCat.Hom.hom
        ((geometricFrobenius p f X).appLE U U (geometricFrobenius_le_preimage p f X U))
      s =
      s ^ p ^ f := sorry

/-- Geometric Frobenius is the identity on the underlying topological space. -/
theorem geometricFrobenius_base (X : SchemeOverField k) :
    (geometricFrobenius p f X).base = 𝟙 (X.left : TopCat) := sorry

/-- The geometric Frobenius of Spec(k) is the identity morphism. -/
theorem geometricFrobenius_id [Fintype k] (hcard : Fintype.card k = p ^ f) :
    geometricFrobenius p f (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      𝟙 (Spec (CommRingCat.of k)) := sorry

end AlgebraicGeometry.SchemeOverField
