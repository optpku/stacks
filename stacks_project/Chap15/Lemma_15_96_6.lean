/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Bockstein

@[expose] public section

/-!
# Lemma 15.96.6: eta reduction and the Bockstein complex

@stack 0F7T
-/

open scoped nonZeroDivisors
open CochainComplex.BerthelotOgus.Int

noncomputable section

universe u v

section


variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
variable (hf : f ∈ nonZeroDivisors A)
variable (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree f K)

/- Lemma 15.96.6, tag `0F7T`: the canonical map from eta reduction to the Bockstein complex is a
quasi-isomorphism. -/
@[stacks 0F7T "eta reduction is quasi-isomorphic to the Bockstein complex"]
#check toBockstein_quasiIso_of_nonZeroDivisor f K hf hK

#check toBockstein f K hK
#check toHomology_comm_operator f K hK

end
