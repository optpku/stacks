/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Homology
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Cohomology on the parasitic Verdier quotient

Typed compatibility checks for localization-valued cohomology, retaining the
module and derived-category prerequisite exports.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open DerivedCategory.CohomologyIn

universe u

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyToQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    DerivedLQCohFbc X ⥤ FppfModules.LQCohFbc.Quotient X)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyToQCoh_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    homologyToQCoh X i = Homology.functor (FppfModules.lqcohFbc X) i ⋙
      FppfModules.LQCohFbc.toQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyToQCoh.instIsHomological :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    (homologyToQCoh X i).IsHomological)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.derivedParasitic_le_homologicalKernel :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    derivedParasitic X ≤ (homologyToQCoh X i).homologicalKernel)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyToQCoh_inverts_trW :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    (derivedParasitic X).trW.IsInvertedBy (homologyToQCoh X i))

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyFunctor :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    DerivedQCoh X ⥤ FppfModules.LQCohFbc.Quotient X)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyFunctor.instIsHomological :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    (homologyFunctor X i).IsHomological)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyFunctor_comp_quotientFunctor :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    quotientFunctor X ⋙ homologyFunctor X i ≅ homologyToQCoh X i)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyFunctor_fac :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ),
    quotientFunctor X ⋙ homologyFunctor X i = homologyToQCoh X i)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.isZero_iff_homology :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (E : DerivedQCoh X),
    IsZero E ↔ ∀ i : ℤ, IsZero ((homologyFunctor X i).obj E))

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh
