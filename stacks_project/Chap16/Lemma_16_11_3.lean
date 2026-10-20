module

public import ReasLib.RingTheory.Approximation.LocalArtinian
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 16.11.3: the source-facing theorem retains the complete polynomial
source-to-target factorization and the condition that the chosen ambient
element avoids the target prime.  The reusable refinement owner does not need
the latter condition. -/
@[stacks 07FI] #check
  fun {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra.IsGeometricallyRegular k A] [IsNoetherianRing A]
    {q : PrimeSpectrum A} {n : ℕ+}
    (P : Algebra.LocalArtinianApproximation.PolynomialFactorisation.{u, v, w}
      (k := k) (A := A) q n)
    (a : A) (ha : a ∉ q.asIdeal) ↦
      Algebra.LocalArtinianApproximation.Factorisation.PowerRefinement.nonempty
        P.factorisation a

/- The presentation-independent RingHom theorem is the reusable core of the
same refinement. -/
#check @RingHom.Artinian.PowerRefinement
#check @RingHom.Artinian.PowerRefinement.nonempty

/- The input factorisation itself is also presentation-independent; the
localized polynomial owner below is only its source-facing specialization. -/
#check @AlgHom.Factorisation.Artinian
#check @AlgHom.Factorisation.Artinian.ofMaps

/- Algebra-compatible consumers use the corresponding AlgHom owner without
repackaging a second copy of the ring-map diagram. -/
#check @AlgHom.Artinian.PowerRefinement
#check @AlgHom.Artinian.PowerRefinement.toRingHom
#check @AlgHom.Artinian.PowerRefinement.nonempty

#check @Algebra.LocalArtinianApproximation.Factorisation.PowerRefinement
#check @Algebra.LocalArtinianApproximation.Factorisation.PowerRefinement.nonempty
