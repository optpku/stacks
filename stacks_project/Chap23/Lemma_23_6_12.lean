/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Tate.Tor.DividedPowers
import StacksCheckRecall

@[expose] public section

universe u

section Canonicality

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-!
# Divided powers on the Tor algebra

Lemma 23.6.12 identifies `Tor_*^R(S, T)` as a canonical strictly graded-commutative algebra with
divided powers. The reusable owner constructs this structure from explicit Tate and base-change
models, identifies its carrier, unit, multiplication, and divided powers, and gives a universal
canonicality specification with existence and uniqueness.

The construction arguments stay explicit: no public algebra is selected from proof-level model
existence. Downstream mathematics can either use an explicit model or reason through the unique
`TateResolution.Tor.IsCanonical` specification.
-/

/- Lemma 23.6.12 (Tag 09PQ): the canonical Mathlib Tor modules carry a unique
strictly graded-commutative divided-power algebra arising from Tate/base-change models. -/
@[stacks 09PQ "canonicality of divided powers on Tor"]
#check (TateResolution.Tor.existsUnique_isCanonical (R := R) (S := S) (T := T) :
  ∃! D : DividedPowerGradedAlgebra R,
    TateResolution.Tor.IsCanonical (S := S) (T := T) D)

end Canonicality

#check @TateResolution.Tor.IsCanonical
#check @TateResolution.Tor.IsCanonical.eq_model
#check @TateResolution.Tor.IsCanonical.eq_algebraOfModel
#check @TateResolution.Tor.IsCanonical.piece
#check @TateResolution.Tor.Polynomial.algebra_isCanonical
#check @TateResolution.Tor.Polynomial.algebra
#check @TateResolution.Tor.transportIso
#check @TateResolution.Tor.Polynomial.algebra_piece
#check @TateResolution.Tor.Polynomial.algebra_one
#check @TateResolution.Tor.Polynomial.algebra_mul
#check @TateResolution.Tor.Polynomial.algebra_gammaPiece
#check @TateResolution.Tor.Polynomial.algebra_eq_of_models
#check @TateResolution.Tor.Polynomial.algebra_eq_of_resolutions
#check @TateResolution.Tor.algebraOfModel
#check @TateResolution.Tor.algebraOfModel_eq_of_covers
#check @TateResolution.Tor.algebraOfModel_eq_of_resolutions
#check @TateResolution.BaseChange.homologyTorEquiv
#check @TateResolution.BaseChange.comparisonComplexIso_trans
#check @TateResolution.BaseChange.comparisonHomologyIso_trans
#check @TateResolution.BaseChange.homologyIso_hom_naturality
#check @DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
#check @DividedPowerGradedAlgebra.transport
