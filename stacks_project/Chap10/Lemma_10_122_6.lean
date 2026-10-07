module

public import ReasLib.RingTheory.QuasiFinite.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.6

The reusable owner is `Algebra.QuasiFiniteAt.iff_awayMul_of_finiteType`.
It keeps the finite-type hypothesis and the source prime `p`, while the
stronger `Algebra.QuasiFiniteAt.iff_awayMul` uses the contracted prime and is
available to later localization arguments.

@stack 077H
-/

/- Lemma 10.122.6: Let `R → S` be a finite type ring map.  If `q ⊂ S` lies
over `p ⊂ R`, `f ∉ p`, and `g ∉ q`, then quasi-finiteness at `q` is equivalent
to quasi-finiteness after passing to
`Localization.Away f → Localization.Away ((algebraMap R S f) * g)`. -/
@[stacks 077H]
#check @Algebra.QuasiFiniteAt.iff_awayMul_of_finiteType

-- The source-facing bridge is backed by a generic statement with no finite-type assumption.
@[stacks 077H "generalized away-product comparison"]
#check @Algebra.QuasiFiniteAt.iff_awayMul

-- These lower-layer declarations are the reusable prime and scalar-action data used by the owner.
#check @Ideal.mapAwayMul
#check @Ideal.mapAwayMul_isPrime
#check @Ideal.comap_mapAwayMul
#check @Ideal.mapAwayMul_liesOver
#check @Localization.Away.Relative.mapMulAlgebra
#check @Localization.Away.Relative.algebraMapMul_isScalarTower
