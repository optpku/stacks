module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Geometric
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry
open AlgebraicGeometry.SchemeOverField

universe u

/- Definition 64.3.4: the geometric Frobenius of a scheme `X` over a finite field
`k` with `q = p ^ f` elements is the morphism π_X : X ⟶ X over Spec(k) which
equals F_X^f. -/
@[stacks 03SQ] #check
  (AlgebraicGeometry.SchemeOverField.geometricFrobeniusOver :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
      [Fintype k] (hcard : Fintype.card k = p ^ f)
      (X : AlgebraicGeometry.SchemeOverField k), X ⟶ X)

#check (AlgebraicGeometry.SchemeOverField.geometricFrobenius :
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    (X : AlgebraicGeometry.SchemeOverField k), X.left ⟶ X.left)

#check (AlgebraicGeometry.SchemeOverField.geometricFrobenius_eq_absoluteFrobeniusPow :
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    (X : AlgebraicGeometry.SchemeOverField k),
    AlgebraicGeometry.SchemeOverField.geometricFrobenius p f X =
      AlgebraicGeometry.Scheme.Hom.absoluteFrobeniusPowSource (p := p) X.hom f)

#check (AlgebraicGeometry.SchemeOverField.geometricFrobenius_comp_hom :
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : AlgebraicGeometry.SchemeOverField k),
    AlgebraicGeometry.SchemeOverField.geometricFrobenius p f X ≫ X.hom = X.hom)
