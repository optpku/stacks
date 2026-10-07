module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints.Charpoly

/-!
# Lemma 15.111.3

@stack 0H34
-/

@[expose] public section

universe u v

open Polynomial

/- Lemma 15.111.3 (current Stacks numbering: Lemma 15.112.3, tag `0H34`):
if a finite group acts on a commutative ring `R`, `J` is an ideal of the fixed subring,
and `x` lies in its extension to `R`, then every nonleading coefficient of
`∏ σ : G, (T - σ • x)` belongs to `J`.  The product and monicity are Mathlib's canonical
orbit-polynomial API; `FixedPoints.charpolyCoeff` supplies the coefficient in the fixed subring.
-/
@[stacks 0H34 "Lemma 15.111.3"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Fintype G]
    (J : Ideal (FixedPoints.subring R G)) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    (i : Fin (Fintype.card G)) ↦
  (FixedPoints.charpolyCoeff_mem G J hx (n := i) i.isLt :
    ⟨(MulSemiringAction.charpoly G x).coeff i,
      fun g ↦ MulSemiringAction.smul_coeff_charpoly x i g⟩ ∈ J)
