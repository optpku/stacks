/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

@[expose] public section

/-!
# Jacobi--Zariski Sequence

@stack 00S2

The four atomic exactness and surjectivity statements in Lemma 10.134.4 are already the
canonical Jacobi--Zariski API.  The textbook sequence is recalled componentwise rather than
repackaged as one conjunction.
-/

/- Lemma 10.134.4 (Jacobi-Zariski sequence), tag 00S2 (1): exactness at
`H¹(L_{S/R})`. -/
@[stacks 00S2 "Jacobi-Zariski exactness at H1"]
#check @Algebra.H1Cotangent.exact_map_δ

/- Lemma 10.134.4 (Jacobi-Zariski sequence), tag 00S2 (2): exactness at
`H¹(L_{T/R})`. -/
@[stacks 00S2 "Jacobi-Zariski exactness after base change"]
#check @Algebra.H1Cotangent.exact_δ_mapBaseChange

/- Lemma 10.134.4 (Jacobi-Zariski sequence), tag 00S2 (3): exactness at the base-changed
Kähler differentials. -/
@[stacks 00S2 "Jacobi-Zariski exactness at Kahler differentials"]
#check @KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 10.134.4 (Jacobi-Zariski sequence), tag 00S2 (4): surjectivity of the terminal
Kähler-differential map. -/
@[stacks 00S2 "Jacobi-Zariski terminal surjectivity"]
#check @KaehlerDifferential.map_surjective
