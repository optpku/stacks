/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Polynomial presentations and formal smoothness

@stack 00TL

Lemma 10.138.5 is the polynomial-ring specialization of
`Algebra.FormallySmooth.iff_split_surjection`.
-/

universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.138.5: a quotient of a polynomial `R`-algebra is formally smooth exactly when
the induced map from the quotient by the square of the presentation kernel admits a section. -/
@[stacks 00TL]
#check Algebra.FormallySmooth.iff_split_surjection
  (R := R) (A := S) (P := MvPolynomial ι R)

end
