module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Homotopy
public import ReasLib.RingTheory.CotangentComplex.Homotopy
import StacksCheckRecall

/-!
# Diagonal factorization of cotangent functoriality

A diagonal factorization of a commutative square of ring maps makes the induced map of
standard resolutions homotopic to the composite through the identity-algebra resolution, and
therefore makes the functoriality map of cotangent complexes homotopic to zero.
-/

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution

universe u

/- Remark 92.6.3 (1): a diagonal making both triangles commute identifies the map of standard
resolutions up to simplicial homotopy with the composite through that diagonal. -/
@[stacks 08SB] #check
  (CategoryTheory.CommRingCat.Under.PolynomialResolution.functorialitySimplicial_homotopic_throughDiagonal :
    ∀ {A B A' B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
      {β : A' ⟶ B'} {φ : B ⟶ B'} (sq : CommSq ρ α β φ) (κ : B ⟶ A')
      (h_left : α ≫ κ = ρ) (h_right : κ ≫ β = φ),
      SimplicialObject.Homotopic
        (functorialitySimplicial_mk α ρ β φ sq.w) (throughDiagonal α β κ))

/- Remark 92.6.3 (2): under the same diagonal hypotheses the scalar-extended functoriality map
of cotangent complexes is homotopic to zero. -/
@[stacks 08SB] #check (Algebra.CotangentComplex.map_homotopic_zero :
  ∀ {A B A' B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
    {β : A' ⟶ B'} {φ : B ⟶ B'} (sq : CommSq ρ α β φ) (κ : B ⟶ A')
    (h_left : α ≫ κ = ρ) (h_right : κ ≫ β = φ),
    Nonempty (Homotopy
      (Algebra.CotangentComplex.map α.hom β.hom ρ.hom φ.hom
        (Algebra.CotangentComplex.commSq_hom sq)) 0))
