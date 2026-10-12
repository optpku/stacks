/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.TorAmplitude
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open ModuleCat.UpperShriek

noncomputable section

universe u

/- Lemma 47.25.8 (1): for a flat finite-type map of Noetherian rings, localized
nonzero cohomology of the relative dualizing complex at `q` can occur only in
degrees `i ∈ Set.Icc (-(d : ℤ)) 0`, where `d` is the local dimension of the fibre
at `q`. -/
@[stacks 0E9Q] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizingCohomology_degree_mem :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
      (hf : (algebraMap R A).FiniteType)
      (presentation : Presentation (algebraMap R A))
      (p : PrimeSpectrum R) (q : PrimeSpectrum A)
      (hq : PrimeSpectrum.comap (algebraMap R A) q = p)
      (d : ℕ) (hd : ringKrullDim (fiberLocalRingAt R A q) = d)
      (i : ℤ)
      (hi : Nontrivial
        (LocalizedModule.AtPrime q.asIdeal
          ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
            (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))),
      i ∈ Set.Icc (-(d : ℤ)) 0)

/- Lemma 47.25.8 (2): if every fibre of a flat finite-type map of Noetherian
rings has Krull dimension at most `d`, then its presentation-defined relative
dualizing complex has Tor amplitude in `[-d, 0]` over the base ring. -/
@[stacks 0E9Q] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_hasTorAmplitudeInOver :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
      (hf : (algebraMap R A).FiniteType)
      (presentation : Presentation (algebraMap R A))
      (d : ℕ) (hfibers : RingHom.FibersKrullDimLE d (algebraMap R A)),
      DerivedCategory.HasTorAmplitudeInOver R
        (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) (-(d : ℤ)) 0)
