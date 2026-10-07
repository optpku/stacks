module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.tilde

/-- For an affine scheme, degreewise tilde sheafification preserves and reflects
`m`-pseudo-coherence of a cochain complex. -/
theorem isMPseudoCoherent_iff
    (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat R) ℤ) (m : ℤ) :
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj M)) m ↔
      CategoryTheory.CochainComplex.IsMPseudoCoherent M m := sorry

/-- For an affine scheme, degreewise tilde sheafification preserves and reflects
pseudo-coherence of a cochain complex. -/
theorem isPseudoCoherent_iff
    (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat R) ℤ) :
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj M)) ↔
      CategoryTheory.CochainComplex.IsPseudoCoherent M := sorry

end AlgebraicGeometry.tilde
