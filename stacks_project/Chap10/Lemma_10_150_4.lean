module

public import ReasLib.RingTheory.DirectLimit.Algebra.FormallyEtale
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.150.4

The fixed-base algebra structure on a directed direct limit, its stage and
universal `AlgHom` maps, and preservation of formal etaleness are owned by the
neutral `Ring.DirectLimit` API in `ReasLib`.

@stack 031N
-/

/- Lemma 10.150.4 [stacks 031N]: if every structure map in a directed system
of commutative `R`-algebras is formally etale, then the canonical map from
`R` to its direct limit is formally etale. The shared API states the result
both as `Algebra.FormallyEtale R (Ring.DirectLimit S ρ)` and as the equivalent
property of the canonical structure map. -/
@[stacks 031N]
#check @Ring.DirectLimit.formallyEtale

#check @Ring.DirectLimit.formallyEtale_algebraMap
#check @Ring.DirectLimit.algebraMap_eq_of
#check @Ring.DirectLimit.ofAlgHom
#check @Ring.DirectLimit.liftAlgHom
