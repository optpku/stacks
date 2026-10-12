/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints
public import ReasLib.RingTheory.Invariant.ResidueField

@[expose] public section

/-!
# Lemma 15.111.9: invariant residue fields

@stack 0BRJ
-/

open scoped Pointwise

universe u v

/-
Lemma 15.111.9 (current Stacks numbering: Lemma 15.112.9, tag `0BRJ`).  Let a finite group `G`
act on a commutative ring `R`, let `p` be a prime ideal of `R^G`, and let `q` be a prime ideal of
`R` lying over `p`.

(1) The residue-field extension `κ(q) / κ(p)` is algebraic and normal.
(2) The decomposition group of `q` surjects onto `Aut(κ(q) / κ(p))`.

The two checks below specialize the reusable invariant residue-field API.  The scoped algebra in
(1) is the map induced by the chosen lying-over pair; it cannot be a global instance because
different pairs can create competing residue-field algebra paths.
-/

section

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

@[stacks 0BRJ "Lemma 15.111.9 (1)"]
#check fun (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
    (q : Ideal R) [q.IsPrime] [q.LiesOver p] ↦
  (Ideal.ResidueField.Invariant.normal G p q :
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Normal p.ResidueField q.ResidueField)

@[stacks 0BRJ "Lemma 15.111.9 (2)"]
#check fun (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
    (q : Ideal R) [q.IsPrime] [q.LiesOver p] ↦
  (Ideal.ResidueField.Invariant.stabilizerHom_surjective G p q :
    Function.Surjective
      (Ideal.ResidueField.Invariant.stabilizerHom G p q))

end
