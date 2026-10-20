module

public import ReasLib.RingTheory.KrullDimension.Integral
import StacksCheckRecall

/-!
# Krull Dimension of Injective Integral Maps

@stack 00OK
-/

@[expose] public section

/- Lemma 10.112.4 (Stacks tag `00OK`): if `R` is identified with a subring of
`S` and `S` is integral over `R`, then their Krull dimensions agree. -/
@[stacks 00OK]
#check @ringKrullDim_eq_of_injective_algebraMap_of_isIntegral

/- The map-first owner of the same dimension equality. -/
@[stacks 00OK "map-first integral dimension equality"]
#check @RingHom.IsIntegral.ringKrullDim_eq_of_injective
