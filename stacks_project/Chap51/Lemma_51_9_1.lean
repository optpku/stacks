module

public import ReasLib.RingTheory.Depth.Openness
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u v

/- Lemma 51.9.1: If a finite module over a Noetherian ring has finite
`I`-depth `e` at `p ∈ V(I)`, then the localized `I`-depth is at least `e` on a
nonempty relatively open subset of `V(p)`. -/
@[stacks 0DWX] #check (Ideal.exists_open_depth_ge :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set A))
    (e : ℕ)
    (hdepth : Ideal.depth (I.localizationAtPrime p)
      (LocalizedModule.AtPrime p.asIdeal M) = (e : ℕ∞)),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      (U ∩ PrimeSpectrum.zeroLocus p.asIdeal).Nonempty ∧
      ∀ q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal,
        (e : ℕ∞) ≤ Ideal.depth (I.localizationAtPrime q)
          (LocalizedModule.AtPrime q.asIdeal M))
