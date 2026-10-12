/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.FiniteStage
public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Localization

/-!
# Affine vanishing-pattern strata

Each vanishing pattern determines the affine locally closed stratum
`Z(E', E'') = Spec((A ⧸ ⟨E''⟩)[∏ E'⁻¹])`, closed in the corresponding
component spectrum `X_{E', E''}`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.WLocalAffine

variable {A : Type u} [CommRing A]

/-- The affine locally closed stratum `Z(E', E'')` attached to a vanishing
pattern, as the spectrum of `(A ⧸ I)_f`. -/
noncomputable abbrev stratum {E : Finset A} (p : VanishingPattern E) : Scheme.{u} :=
  Spec (CommRingCat.of (stratumSections p))

/-- The closed immersion of a stratum into the component spectrum
`X_{E', E''} = Spec(A_Z^~)`. -/
noncomputable def stratumι {E : Finset A} (p : VanishingPattern E) :
    stratum p ⟶ componentScheme p :=
  Spec.map (CommRingCat.ofHom (toSections p))

/-- Each vanishing-pattern stratum is a closed subscheme of its component
spectrum. -/
instance instIsClosedImmersion_stratumι {E : Finset A} (p : VanishingPattern E) :
    IsClosedImmersion (stratumι p) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (toSections p))
    (toSections_surjective p)

end AlgebraicGeometry.Scheme.WLocalAffine
