/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.GeometricRegularity.Local

/-!
# Geometric regularity criteria

This file recalls the canonical positive-characteristic local criterion.

@stack 07E5
-/

@[expose] public section

/- Proposition 15.35.1, tag `07E5`: the
geometric-regularity, purely inseparable, cotangent-homology, and differential
criteria are equivalent. -/
@[stacks 07E5 "Proposition 15.35.1"]
#check @Algebra.geometricallyRegularLocalRing_tfae_of_charP

/- Proposition 15.35.1, condition (3): the library-facing homology map is
injective exactly when the canonical map to `maximalIdeal A / maximalIdeal A ^ 2`
is injective. -/
#check @Algebra.H1Cotangent.ResidueField.toCotangent_injective_iff

/- Proposition 15.35.1, condition (4): the differential criterion uses the
canonical residue-field comparison map. -/
#check @KaehlerDifferential.residueFieldComparison
