/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The endofunctor of modules taking sections supported on `T`. -/
abbrev sectionsWithSupport (T : Set (PrimeSpectrum A)) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  coreflector T ⋙ inclusion T

/-- The degree-`degree` cohomology of bounded-below derived sections supported on `T`. -/
abbrev cohomologyPlus (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (degree : ℤ) : ModuleCat.{u} A :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) degree).obj
    ((sectionsWithSupport T).rightDerivedFunctorPlus.obj K)

end CategoryTheory.ModuleCat.SupportedOn
