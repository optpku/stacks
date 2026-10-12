/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

/-!
# Polynomial-affine diagrams over the small Zariski site

The comma category of maps from open subschemes to polynomial affine schemes
has a canonical projection to the small Zariski site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- An affine scheme over `Spec Λ` is polynomial affine if it is isomorphic over
`Spec Λ` to affine space on some type of variables. -/
def isPolynomialAffine (Λ : CommRingCat.{u}) : ObjectProperty (Over (Spec Λ)) :=
  fun target ↦ ∃ vars : Type u,
    Nonempty (target ≅ (AffineSpace vars (Spec Λ)).asOver (Spec Λ))

/-- Polynomial-affineness is equivalent to being isomorphic over `Spec Λ` to
the spectrum of a polynomial `Λ`-algebra. -/
theorem isPolynomialAffine_iff (Λ : CommRingCat.{u}) (target : Over (Spec Λ)) :
    isPolynomialAffine Λ target ↔ ∃ vars : Type u,
      Nonempty (target ≅ Over.mk (Spec.map
        (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial vars Λ)))) := sorry

/-- The category of diagrams `U ⟶ A` over `Spec Λ`, with `U` an open subscheme
of `X` and `A` polynomial affine over `Spec Λ`; morphisms are commuting squares. -/
abbrev category (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :=
  Comma (X.smallZariskiForget ⋙ Over.map (X ↘ Spec Λ)) (isPolynomialAffine Λ).ι

/-- The projection sending a polynomial-affine diagram to its open subscheme. -/
def forgetZariski (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    category Λ X ⥤ X.smallZariskiSite :=
  Comma.fst (X.smallZariskiForget ⋙ Over.map (X ↘ Spec Λ)) (isPolynomialAffine Λ).ι

end AlgebraicGeometry.Scheme.CotangentSite
