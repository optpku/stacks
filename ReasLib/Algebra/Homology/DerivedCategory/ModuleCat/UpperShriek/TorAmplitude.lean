module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.FiberDimension
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
public import ReasLib.RingTheory.RingHom.Fiber.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

/-- For a flat finite-type map of Noetherian rings, nonzero localized cohomology of
the presentation-defined relative dualizing object occurs only between the negative
local dimension of the fibre and degree zero. -/
theorem relativeDualizingCohomology_degree_mem
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
    (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap (algebraMap R A) q = p)
    (d : ℕ) (hd : ringKrullDim (fiberLocalRingAt R A q) = d)
    (i : ℤ)
    (hi : Nontrivial
      (LocalizedModule.AtPrime q.asIdeal
        ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
          (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))) :
    i ∈ Set.Icc (-(d : ℤ)) 0 := sorry

/-- If the fibres of a flat finite-type map of Noetherian rings have Krull dimension
at most `d`, its presentation-defined relative dualizing object has Tor amplitude
in `[-d, 0]` over the base ring. -/
theorem relativeDualizing_hasTorAmplitudeInOver
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
    (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
    (d : ℕ) (hfibers : RingHom.FibersKrullDimLE d (algebraMap R A)) :
    DerivedCategory.HasTorAmplitudeInOver R
      (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) (-(d : ℤ)) 0 := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
