/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Site

/-!
# Polynomial affine realizations

Polynomial presentations give explicit objects in the category of diagrams
from open subschemes to polynomial affine schemes. Arbitrary objects retain
only their canonical target, rather than a chosen polynomial presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- The spectrum of the polynomial algebra on the specified variables. -/
abbrev specPolynomial (Λ : CommRingCat.{u}) (vars : Type u) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial vars Λ))

/-- The base morphism of the spectrum of a polynomial algebra. -/
abbrev specPolynomialToBase (Λ : CommRingCat.{u}) (vars : Type u) :
    specPolynomial Λ vars ⟶ Spec Λ :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial vars Λ))

/-- An explicit polynomial affine diagram defines an object of the canonical
comma category of polynomial affine diagrams. -/
def ofPolynomial {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) (vars : Type u)
    (hom : U.left ⟶ specPolynomial Λ vars)
    (w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ (X ↘ Spec Λ)) :
    category Λ X where
  left := U
  right := ⟨Over.mk (specPolynomialToBase Λ vars),
    (isPolynomialAffine_iff Λ _).mpr ⟨vars, ⟨Iso.refl _⟩⟩⟩
  hom := Over.homMk hom w

/-- The functor sending a polynomial affine diagram to its target scheme. -/
def affineRealization (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    category Λ X ⥤ Scheme.{u} :=
  Comma.snd _ _ ⋙ (isPolynomialAffine Λ).ι ⋙ Over.forget (Spec Λ)

end AlgebraicGeometry.Scheme.CotangentSite
