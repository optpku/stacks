/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Pair

@[expose] public section

/-!
# Lemma 15.96.8: product decomposition of the reduced eta pair

@stack 0F7Z
-/

open scoped nonZeroDivisors
open CochainComplex.BerthelotOgus.Int.Reduction.Pair

noncomputable section

universe u v

section


variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
variable (hf : f ∈ nonZeroDivisors A)
variable (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree f K)
variable (hsurj : HomologicalComplex.Bockstein.CyclesLift f K i)

/- Lemma 15.96.8, tag `0F7Z`: the canonical reduced eta pair identifies its source with a
product of submodules of its two coordinate targets. -/
@[stacks 0F7Z "product decomposition for the reduced Berthelot-Ogus eta pair"]
#check pairLinear_identifiesWithProdSubmodules_of_nonZeroDivisor f K i hf hK hsurj

#check pairLinear f K i hK

-- Canonical downstream use bundles termwise regularity in the eta domain.
#check @CochainComplex.BerthelotOgus.Int.Reduction.Pair.linear
#check @CochainComplex.BerthelotOgus.Int.Reduction.Pair.identifiesWithProdSubmodules

end
