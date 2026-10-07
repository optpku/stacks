module

public import ReasLib.RingTheory.Ideal.FlatQuotient.CotangentSections
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u v

/- Lemma 38.25.12: let `A` be a local ring, `I : Ideal A`, and
`U : Opens (PrimeSpectrum A)` be quasi-compact. If `M / IM` is flat over `A / I` and `M`
is flat over `U`, then `M / I₂M` is flat over `A / I₂`, where
`I₂ = I.cotangentSectionsKernel U`. -/
@[stacks 0ATC] #check
  (Ideal.IsFlatQuotient.cotangentSectionsKernel :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A]
      (I : Ideal A) (U : TopologicalSpace.Opens (PrimeSpectrum A)) (M : Type v)
      [AddCommGroup M] [Module A M],
      IsCompact (U : Set (PrimeSpectrum A)) →
        I.IsFlatQuotient M →
          (U : Set (PrimeSpectrum A)) ⊆ Module.flatOverBaseLocus A A M →
            (I.cotangentSectionsKernel U).IsFlatQuotient M)
