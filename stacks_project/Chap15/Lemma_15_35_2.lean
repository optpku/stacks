module

import StacksCheckRecall
public import ReasLib.FieldTheory.GeometricRegularity.LocalizedPolynomial

/-!
# Localized polynomial approximations

This file recalls the flatness and regular-closed-fiber conclusions for a
geometrically regular local algebra.

@stack 07E6
-/

@[expose] public section

/- Lemma 15.35.2 (1), tag `07E6`: the canonical map
from the localized polynomial presentation is flat. -/
@[stacks 07E6 "Lemma 15.35.2 (1)"]
#check @Algebra.IsGeometricallyRegular.localizedPolynomial_map_flat

/- Lemma 15.35.2 (2), tag `07E6`: its closed fiber is
a regular local ring. -/
@[stacks 07E6 "Lemma 15.35.2 (2)"]
#check @Algebra.IsGeometricallyRegular.localizedPolynomial_closedFiber_regular

/- The source map is the canonical localization map at the contracted closed
point, rather than a chapter-local reconstruction. -/
#check @RingHom.LocalTarget.mapAtClosedPoint
