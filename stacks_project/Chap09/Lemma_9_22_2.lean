module

public import Mathlib.FieldTheory.Galois.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 9.22.2 (Tag 0BMK): for a normal field tower, restriction from `Gal(L / K)` to
`Gal(M / K)` is surjective and continuous in the Krull topologies. -/
universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [IsGalois K L] [IsGalois K M]

@[stacks 0BMK]
#check (AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K))
#check (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
#check (InfiniteGalois.restrictNormalHom_continuous (k := K) (K := L) M)
