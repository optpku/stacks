/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Homology
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Homological
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.FppfSerreQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent

/-!
# Cohomology of D_QCoh on an algebraic stack

Degree-`i` cohomology on `DerivedLQCohFbc` composed with the Serre quotient
`Q` inverts the Verdier system of parasitic cohomology, and therefore factors
uniquely through `DerivedQCoh` as a cohomological functor
`H^i : DerivedQCoh X ⥤ FppfModules.LQCohFbc.Quotient X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty CategoryTheory.ObjectProperty.VerdierQuotient
open AlgebraicGeometry.GroupoidsOver
open DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

variable {S : Scheme.{u}}

/-- The composite of lifted cohomology on `DerivedLQCohFbc X` with the Serre
quotient `toQCoh`. -/
def homologyToQCoh (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    DerivedLQCohFbc X ⥤ FppfModules.LQCohFbc.Quotient X :=
  Homology.functor (FppfModules.lqcohFbc X) i ⋙ FppfModules.LQCohFbc.toQCoh X

/-- `homologyToQCoh X i` is lifted cohomology postcomposed with `toQCoh`. -/
theorem homologyToQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    homologyToQCoh X i =
      Homology.functor (FppfModules.lqcohFbc X) i ⋙
        FppfModules.LQCohFbc.toQCoh X := sorry

/-- The composite of lifted cohomology on `DerivedLQCohFbc X` with the Serre
quotient `toQCoh` is homological. -/
instance homologyToQCoh.instIsHomological (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (homologyToQCoh X i).IsHomological := sorry

/-- Objects with parasitic cohomology lie in the homological kernel of
`homologyToQCoh X i`. -/
theorem derivedParasitic_le_homologicalKernel (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    derivedParasitic X ≤ (homologyToQCoh X i).homologicalKernel := sorry

/-- The composite `homologyToQCoh X i` inverts the Verdier system of parasitic
cohomology. -/
theorem homologyToQCoh_inverts_trW (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (derivedParasitic X).trW.IsInvertedBy (homologyToQCoh X i) := sorry

/-- Degree-wise cohomology on the parasitic Verdier quotient, valued in the
Serre localization of locally quasi-coherent fppf modules with flat base change. -/
def homologyFunctor (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    DerivedQCoh X ⥤ FppfModules.LQCohFbc.Quotient X :=
  Homological.factor (derivedParasitic X) (homologyToQCoh X i)
    (homologyToQCoh_inverts_trW X i)

/-- `homologyFunctor X i` is a homological functor. -/
instance homologyFunctor.instIsHomological (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (homologyFunctor X i).IsHomological := sorry

/-- The canonical comparison identifying
`quotientFunctor X ⋙ homologyFunctor X i` with `homologyToQCoh X i`. -/
def homologyFunctor_comp_quotientFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    quotientFunctor X ⋙ homologyFunctor X i ≅ homologyToQCoh X i :=
  Homological.factor.facIso (derivedParasitic X) (homologyToQCoh X i)
    (homologyToQCoh_inverts_trW X i)

/-- Strict factorization of `homologyFunctor X i` through
`quotientFunctor X`. -/
theorem homologyFunctor_fac (X : GroupoidsOver S) [AlgebraicStack X]
    (i : ℤ) :
    quotientFunctor X ⋙ homologyFunctor X i = homologyToQCoh X i := sorry

/-- An object of the parasitic Verdier quotient is zero if and only if all
of its cohomology objects in the parasitic Serre localization vanish. -/
theorem isZero_iff_homology {X : GroupoidsOver S} [AlgebraicStack X]
    (E : DerivedQCoh X) :
    IsZero E ↔ ∀ i : ℤ, IsZero ((homologyFunctor X i).obj E) := sorry

/-- Degree-wise cohomology on the derived category of quasi-coherent modules,
valued in quasi-coherent fppf modules. -/
def cohomologyFunctor (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    DerivedQCoh X ⥤ GroupoidsOver.QCoh X :=
  homologyFunctor X i ⋙ FppfModules.LQCohFbc.quotientToQCoh X

/-- Pulling quasi-coherent cohomology back along the Verdier quotient gives
lifted cohomology followed by the fppf quasi-coherent coreflector. -/
def cohomologyFunctor_comp_quotientFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    quotientFunctor X ⋙ cohomologyFunctor X i ≅
      Homology.functor (FppfModules.lqcohFbc X) i ⋙
        FppfModules.LQCohFbc.coreflector X :=
  (Functor.associator (quotientFunctor X) (homologyFunctor X i)
    (FppfModules.LQCohFbc.quotientToQCoh X)).symm ≪≫
  Functor.isoWhiskerRight (homologyFunctor_comp_quotientFunctor X i)
    (FppfModules.LQCohFbc.quotientToQCoh X) ≪≫
  Functor.associator (Homology.functor (FppfModules.lqcohFbc X) i)
    (FppfModules.LQCohFbc.toQCoh X) (FppfModules.LQCohFbc.quotientToQCoh X) ≪≫
  Functor.isoWhiskerLeft (Homology.functor (FppfModules.lqcohFbc X) i)
    (FppfModules.LQCohFbc.toQCoh_comp_quotientToQCoh X)

/-- Quasi-coherent cohomology in each degree is a homological functor. -/
instance cohomologyFunctor.instIsHomological (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (cohomologyFunctor X i).IsHomological := sorry

/-- An object of the derived category of quasi-coherent modules is zero if
and only if every quasi-coherent cohomology object vanishes. -/
theorem isZero_iff_cohomology {X : GroupoidsOver S} [AlgebraicStack X]
    (E : DerivedQCoh X) :
    IsZero E ↔ ∀ i : ℤ, IsZero ((cohomologyFunctor X i).obj E) := sorry

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh
