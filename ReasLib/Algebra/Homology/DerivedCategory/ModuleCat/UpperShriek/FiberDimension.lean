/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.RingTheory.RingHom.Fiber.Local

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

/-- For a finite-type map of Noetherian rings, nonvanishing of localized degree-`i`
cohomology of a presentation-defined upper-shriek object forces `i` to be at least
the negative local dimension of the fibre. -/
theorem neg_fiberDimension_le_of_localizedCohomology_nontrivial
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap (algebraMap R A) q = p)
    (d : ℕ) (hd : ringKrullDim (fiberLocalRingAt R A q) = d)
    (i : ℤ)
    (hi : Nontrivial
      (LocalizedModule.AtPrime q.asIdeal
        ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
          (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))) :
    -(d : ℤ) ≤ i := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
