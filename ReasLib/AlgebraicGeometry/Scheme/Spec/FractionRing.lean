module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair

/-!
# Affine spectra of fraction-subring pairs

This leaf is the scheme-facing layer for a
`FractionRing.SubringPair`.  It names only the two affine maps induced by the
intersection inclusions; ring-theoretic data stays in the corresponding
RingTheory leaf.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

/-- The affine morphism from the spectrum of the left component to the
spectrum of the intersection. -/
noncomputable def specLeft (P : FractionRing.SubringPair K) :
    Spec (CommRingCat.of P.left) ⟶ Spec (CommRingCat.of P.intersection) :=
  Spec.map (CommRingCat.ofHom P.toLeft)

/-- The affine morphism from the spectrum of the right component to the
spectrum of the intersection. -/
noncomputable def specRight (P : FractionRing.SubringPair K) :
    Spec (CommRingCat.of P.right) ⟶ Spec (CommRingCat.of P.intersection) :=
  Spec.map (CommRingCat.ofHom P.toRight)

end FractionRing.SubringPair
