module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Homology.LocalCohomology.Support
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

universe u

namespace localCohomology

/-- For finitely generated ideals `J ≤ I`, power-annihilation by `J` of the
degree-`i` local cohomology of the regular module supported on `V(I)` implies
power-annihilation by `J` of the same local cohomology of every finitely presented
module that is finite locally free after localization at each `f ∈ I`. -/
@[stacks 0BPX]
theorem isAnnihilatedByPower_of_finiteLocallyFreeAway
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J I : Ideal A) (hJ : J.FG) (hI : I.FG)
    (hJI : J ≤ I) (i : ℕ)
    (hA : Module.IsAnnihilatedByPower J
      ((localCohomology.withSupport I i).obj (ModuleCat.of A A)))
    (hM : ∀ f ∈ I,
      Module.FiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)) :
    Module.IsAnnihilatedByPower J
      ((localCohomology.withSupport I i).obj (ModuleCat.of A M)) := sorry

end localCohomology
