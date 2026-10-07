module

public import Mathlib.Algebra.Ring.Pi
public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.SigmaSpec
public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Stratum

/-!
# Closed subschemes of finite vanishing-pattern stages

The coproduct of the affine strata `Z(E', E'')` is a closed subscheme of
`X_E = Spec(∏ A_Z^~)`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.WLocalAffine

variable {A : Type u} [CommRing A]

/-- The closed subscheme `Z_E` attached to a finite subset, as the coproduct of
the affine vanishing-pattern strata. -/
noncomputable abbrev closed (E : Finset A) : Scheme.{u} :=
  ∐ fun p : VanishingPattern E ↦ stratum p

/-- The product of the canonical surjections `A_Z^~ → (A ⧸ I)_f` over vanishing
patterns of `E`. -/
noncomputable def piToSections (E : Finset A) :
    ((p : VanishingPattern E) → componentRingCat p) →+*
      ((p : VanishingPattern E) → CommRingCat.of (stratumSections p)) :=
  RingHom.pi fun p ↦
    (toSections p).comp (Pi.evalRingHom (fun q : VanishingPattern E ↦ componentRingCat q) p)

/-- The product of the canonical stratum surjections is surjective. -/
theorem piToSections_surjective (E : Finset A) :
    Function.Surjective (piToSections E) :=
  sorry

/-- The identification of `Z_E` with the spectrum of the product of the
stratum section rings. -/
noncomputable def closedIso (E : Finset A) :
    closed E ≅
      ProductSpectrum.family fun p : VanishingPattern E ↦
        CommRingCat.of (stratumSections p) :=
  ProductSpectrum.sigmaSpecIso fun p : VanishingPattern E ↦
    CommRingCat.of (stratumSections p)

/-- The closed subscheme morphism `Z_E ⟶ X_E`. -/
noncomputable def closedι (E : Finset A) : closed E ⟶ scheme E :=
  sigmaSpec (fun p : VanishingPattern E ↦ CommRingCat.of (stratumSections p)) ≫
    Spec.map (CommRingCat.ofHom (piToSections E))

/-- The affine comparison `Spec(∏ (A ⧸ I)_f) ⟶ Spec(∏ A_Z^~)` is a closed
immersion. -/
instance instIsClosedImmersion_specMap_piToSections (E : Finset A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (piToSections E))) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (piToSections E))
    (piToSections_surjective E)

/-- The morphism `Z_E ⟶ X_E` is a closed immersion. -/
instance instIsClosedImmersion_closedι (E : Finset A) :
    IsClosedImmersion (closedι E) :=
  IsClosedImmersion.comp
    (sigmaSpec (fun p : VanishingPattern E ↦ CommRingCat.of (stratumSections p)))
    (Spec.map (CommRingCat.ofHom (piToSections E)))

/-- Coproduct inclusions into `Z_E` recover the component closed immersions of
the individual strata. -/
theorem closedι_comp_ι {E : Finset A} (p : VanishingPattern E) :
    Sigma.ι (fun q : VanishingPattern E ↦ stratum q) p ≫ closedι E =
      stratumι p ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun q : VanishingPattern E ↦ componentRingCat q) p)) :=
  sorry

end AlgebraicGeometry.Scheme.WLocalAffine
