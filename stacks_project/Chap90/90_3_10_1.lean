/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCheckRecall

@[expose]
public section

/- 90.3.10.1: for a surjective Λ-algebra map A → k, the conormal sequence
(ker (algebraMap A k)).Cotangent ⟶ Ω[A⁄Λ] ⊗[A] k ⟶ Ω[k⁄Λ] ⟶ 0
is mathlib's surjective conormal sequence. The source map d_A is
`KaehlerDifferential.kerCotangentToTensor Λ A k`; the next map is
`KaehlerDifferential.mapBaseChange Λ A k`. Mathlib writes the middle module as
k ⊗[A] Ω[A⁄Λ] (the source tensor order is `TensorProduct.comm` of this).
Exactness at the middle is `exact_kerCotangentToTensor_mapBaseChange`; the
terminal 0 is `mapBaseChange_surjective`. -/
@[stacks 06S6] #check @KaehlerDifferential.kerCotangentToTensor
@[stacks 06S6] #check @KaehlerDifferential.mapBaseChange
@[stacks 06S6] #check @KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
@[stacks 06S6] #check @KaehlerDifferential.mapBaseChange_surjective
