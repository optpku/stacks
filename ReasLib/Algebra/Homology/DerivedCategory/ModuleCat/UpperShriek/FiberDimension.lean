/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.Topology.KrullDimension.Local

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
    (d : ℕ)
    (hd : topologicalKrullDimAt (fiberPrimeAt R A q) = (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial
      (LocalizedModule.AtPrime q.asIdeal
        ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
          (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))) :
    -(d : ℤ) ≤ i := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
