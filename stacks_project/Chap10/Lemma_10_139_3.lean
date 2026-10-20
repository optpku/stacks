module

public import ReasLib.RingTheory.Extension.Cotangent.Conormal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.139.3

@stack 06A9
-/

/- Lemma 10.139.3 [stacks 06A9]: canonical recall of the conormal sequence of a formally
smooth presentation over a surjective base map.  The source tower is obtained by taking its
associated `Algebra.Extension`; map, exactness, injectivity, and endpoint surjectivity are kept
as independent reusable API. -/
@[stacks 06A9]
#check @Algebra.Extension.Conormal.map

@[stacks 06A9]
#check @Algebra.Extension.Conormal.exact_map_cotangentComplex

@[stacks 06A9]
#check @Algebra.Extension.Conormal.map_injective

@[stacks 06A9]
#check @Algebra.Extension.Conormal.cotangentComplex_surjective
