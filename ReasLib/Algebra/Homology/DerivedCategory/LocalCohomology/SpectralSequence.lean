module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.SectionsWithSupport
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Composition
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Existence
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Spectral sequence for successive local cohomology

The Grothendieck spectral sequence for successive sections-with-support functors abuts to
derived sections supported in the supremum of the two ideals.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Functor.RightDerived

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- A bounded-below derived module admits the Grothendieck spectral sequence for successive
sections supported in two finitely generated ideals, abutting to support in their supremum. -/
theorem existsSpectralSequence (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (K : DerivedCategory.Plus (ModuleCat A)) :
    Nonempty
      (Grothendieck.SpectralSequence
        (ModuleCat.IdealPowerTorsion.sectionsWithSupport J)
        (Bounded.functor
          (ModuleCat.IdealPowerTorsion.sectionsWithSupport I))
        (Bounded.functor
          (ModuleCat.IdealPowerTorsion.sectionsWithSupport (I ⊔ J))) K) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
