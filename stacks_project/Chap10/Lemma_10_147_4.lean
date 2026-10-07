module

public import Mathlib.RingTheory.Smooth.IntegralClosure
import StacksCheckRecall

/-! @stack 03GF -/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.147.4: if `R → S` is smooth, `A = integralClosure R B`, and
`A' = integralClosure S (S ⊗[R] B)`, then the canonical map
`S ⊗[R] A → A'` is bijective, hence an isomorphism. This is exactly the canonical theorem
`TensorProduct.toIntegralClosure_bijective_of_smooth`. -/
@[stacks 03GF "integral closure commutes with smooth base change"]
#check @TensorProduct.toIntegralClosure_bijective_of_smooth
