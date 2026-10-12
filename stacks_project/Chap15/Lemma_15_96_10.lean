/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.BaseChange

@[expose] public section

/-!
# Lemma 15.96.10: flat base change for the eta operator

@stack 0GSR
-/

open scoped nonZeroDivisors

universe u v w

/- Lemma 15.96.10 (1), tag `0GSR`: a flat algebra sends nonzerodivisors to
nonzerodivisors. -/
@[stacks 0GSR "nonzerodivisors under flat base change"] #check
  @Module.Flat.algebraMap_mem_nonZeroDivisors

/- Lemma 15.96.10 (2), tag `0GSR`: flat scalar extension preserves termwise
torsion-freeness. -/
@[stacks 0GSR "termwise torsion-freeness under flat base change"] #check
  (fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [Module.Flat A B] (f : A) (hf : f ∈ nonZeroDivisors A)
      (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
      (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree f K) ↦
    CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree.scalarExtension (B := B) hK)

/- Lemma 15.96.10 (3), tag `0GSR`: the canonical comparison from the scalar extension of
`η[f] K` to the eta complex of the scalar extension is an isomorphism. -/
@[stacks 0GSR "Berthelot-Ogus eta commutes with flat base change"] #check
  (fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [Module.Flat A B] (f : A) (hf : f ∈ nonZeroDivisors A)
      (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
      (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree f K) ↦
    CochainComplex.BerthelotOgus.Int.BaseChange.comparisonIsIso (B := B) f K hK)
