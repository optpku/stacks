/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.FormallyEtale
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']

/-!
# Lemma 10.150.7

@stack 0H93

For a formally etale map `S → S'`, the source compares the nilpotent
thickenings of the diagonal after tensor base change and identifies the
corresponding Kähler differential map.  Both parts are canonical recalls:
the quotient comparison is owned by `KaehlerDifferential`, while the
differential comparison is already a mathlib linear equivalence.
-/

namespace KaehlerDifferential

/- Lemma 10.150.7 (1): for a formally etale map `S → S'`, the canonical
comparison on the `(k + 1)`-st diagonal thickenings is bijective.  The
arbitrary-power owner below is the same statement with `n := k + 1`. -/
@[stacks 0H93 "(1)"]
#check @KaehlerDifferential.diagonalQuotientMap_pow_bijective

/- Lemma 10.150.7 (2): for a formally etale map `S → S'`, the canonical map
`S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R]` is the equivalence
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`. -/
@[stacks 0H93 "(2)"]
#check @KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale

#print axioms KaehlerDifferential.diagonalQuotientMap_pow_bijective
#print axioms KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale

end KaehlerDifferential

end
