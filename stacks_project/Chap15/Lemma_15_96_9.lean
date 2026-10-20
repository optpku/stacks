/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Mul

@[expose] public section

/-!
# Lemma 15.96.9

@stack 0F7U
-/

open scoped nonZeroDivisors

universe u v

/- Lemma 15.96.9, tag `0F7U`: for nonzerodivisors `f` and `g`, if `f * g` acts
injectively in every integer degree of `K`, the source equality is represented by the canonical
isomorphism between the iterated divided-differential eta complex and eta for `f * g`. -/
@[stacks 0F7U "multiplicativity of the Berthelot-Ogus eta operator"] #check
  (fun {A : Type u} [CommRing A] (f g : A)
      (hf : f ∈ nonZeroDivisors A) (hg : g ∈ nonZeroDivisors A)
      (K : CochainComplex (ModuleCat.{v} A) ℤ)
      (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree (f * g) K) ↦
    CochainComplex.BerthelotOgus.Int.Mul.isoOfRegular f g K hK)
