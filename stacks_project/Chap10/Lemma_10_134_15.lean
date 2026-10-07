module

public import ReasLib.RingTheory.Extension.Cotangent.PresentationStability
import StacksCheckRecall

/-!
@stack 00S5
-/

@[expose] public section

/- Lemma 10.134.15 [stacks 00S5]: canonical recall of stable presentation-independence for
finite conormal modules.  The reusable owner is
`Algebra.Generators.Cotangent.stableEquivFree`; the intermediate owner APIs
`complexTermStableEquiv`, `liftStableEquiv`, and `stableEquiv` retain the corresponding
chain-complex, lifted, and coordinate-free forms. -/
@[stacks 00S5]
#check @Algebra.Generators.Cotangent.stableEquivFree

@[stacks 00S5 "stable complex-term equivalence"]
#check @Algebra.Generators.Cotangent.complexTermStableEquiv

@[stacks 00S5 "stable lifted equivalence"]
#check @Algebra.Generators.Cotangent.liftStableEquiv

@[stacks 00S5 "stable coordinate-free equivalence"]
#check @Algebra.Generators.Cotangent.stableEquiv
