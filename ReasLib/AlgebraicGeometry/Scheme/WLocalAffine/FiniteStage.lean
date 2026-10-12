/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.SigmaSpec
public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Component

/-!
# Affine schemes attached to vanishing patterns

The product ring `A_E` of the component localizations is realized as an affine
scheme `X_E = Spec(A_E)`, identified with the coproduct of the component
spectra via the finite `sigmaSpec` comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.WLocalAffine

variable {A : Type u} [CommRing A]

/-- The component localization as an object of `CommRingCat`. -/
noncomputable abbrev componentRingCat {E : Finset A} (p : VanishingPattern E) :
    CommRingCat.{u} :=
  CommRingCat.of (componentAlgebra p)

/-- The product ring `A_E` of the component localizations indexed by vanishing
patterns on `E`. -/
noncomputable abbrev ring (E : Finset A) : Type u :=
  (p : VanishingPattern E) → componentAlgebra p

/-- The affine scheme `X_E`, defined as the spectrum of the product ring `A_E`. -/
noncomputable abbrev scheme (E : Finset A) : Scheme.{u} :=
  ProductSpectrum.family fun p : VanishingPattern E ↦ componentRingCat p

/-- The scheme `X_E` is definitionally `Spec` of the product ring `A_E`. -/
theorem scheme_eq_spec (E : Finset A) :
    scheme E = Spec (CommRingCat.of (ring E)) := sorry

/-- The affine scheme `X_{E', E''}` of a single component localization. -/
noncomputable abbrev componentScheme {E : Finset A} (p : VanishingPattern E) :
    Scheme.{u} :=
  Spec (componentRingCat p)

/-- The canonical identification of `X_E` with the coproduct of the component
spectra `X_{E', E''}`. -/
noncomputable def sigmaIso (E : Finset A) :
    (∐ fun p : VanishingPattern E ↦ componentScheme p) ≅ scheme E :=
  ProductSpectrum.sigmaSpecIso fun p ↦ componentRingCat p

/-- Coproduct inclusions into `X_E` are the spectra of the product projections. -/
theorem ι_comp_sigmaIso (E : Finset A) (p : VanishingPattern E) :
    Sigma.ι (fun q : VanishingPattern E ↦ componentScheme q) p ≫ (sigmaIso E).hom =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun q : VanishingPattern E ↦ componentAlgebra q) p)) := sorry

/-- The scheme `X_E` is affine. -/
instance instIsAffineScheme (E : Finset A) : IsAffine (scheme E) :=
  inferInstance

end AlgebraicGeometry.Scheme.WLocalAffine
