/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import stacks_project.Chap58.Theorem_58_6_2_Fiber
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

universe u

/-- The named compatibility view of the generic action equivalence at a geometric fiber. -/
theorem finiteEtaleFiber_functorToContAction_isEquivalence
    {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X) :
    (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
  CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
    (GeometricPoint.finiteFiber xbar)

/-- The named compatibility view of the continuous base-point-change equivalence. -/
noncomputable abbrev autIso_of_geometricPoints {X : Scheme.{u}} [ConnectedSpace X]
    {xbar xbar' : GeometricPoint X}
    (t : standardFiniteEtaleFiber xbar ≅ standardFiniteEtaleFiber xbar') :
    Aut (standardFiniteEtaleFiber xbar) ≃ₜ* Aut (standardFiniteEtaleFiber xbar') :=
  GeometricPoint.autEquiv t

section

variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)

/- Theorem 58.6.2 (1) -/
@[stacks 0BND] #check
  (CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
    (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar) :
    (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).IsEquivalence)

end

/- Theorem 58.6.2 (2) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.existsIso_finiteFiber :
    ∀ {X : Scheme.{u}} [ConnectedSpace X] (xbar xbar' : GeometricPoint X),
      Nonempty (GeometricPoint.finiteFiber xbar ≅ GeometricPoint.finiteFiber xbar'))

/- Theorem 58.6.2 (3) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.autEquiv :
    ∀ {X : Scheme.{u}} [ConnectedSpace X] {xbar xbar' : GeometricPoint X},
      (GeometricPoint.finiteFiber xbar ≅ GeometricPoint.finiteFiber xbar') →
        Aut (GeometricPoint.finiteFiber xbar) ≃ₜ*
          Aut (GeometricPoint.finiteFiber xbar'))

/- Theorem 58.6.2 (4) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.autEquiv_conj :
    ∀ {X : Scheme.{u}} [ConnectedSpace X]
      {xbar xbar' : GeometricPoint X}
      (t t' : GeometricPoint.finiteFiber xbar ≅ GeometricPoint.finiteFiber xbar'),
      ∃ g : Aut (GeometricPoint.finiteFiber xbar'), ∀ σ : Aut (GeometricPoint.finiteFiber xbar),
        GeometricPoint.autEquiv t' σ = g * GeometricPoint.autEquiv t σ * g⁻¹)

/- Theorem 58.6.2 (5) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap :
    ∀ {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
      (f : X ⟶ Y) (xbar : GeometricPoint X),
      Aut (GeometricPoint.finiteFiber xbar) →ₜ*
        Aut (GeometricPoint.finiteFiber (GeometricPoint.map xbar f)))

/- Theorem 58.6.2 (6) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap_catCommSq :
    ∀ {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
      (f : X ⟶ Y) (xbar : GeometricPoint X),
      Nonempty (CatCommSq (finiteEtaleBaseChange f)
        (GeometricPoint.fiberAction (GeometricPoint.map xbar f))
        (GeometricPoint.fiberAction xbar)
        (GeometricPoint.fundamentalGroupRestriction f xbar)))

/- Theorem 58.6.2 (7) -/
@[stacks 0BND] #check   (AlgebraicGeometry.Scheme.GeometricPoint.autEquiv_catCommSq :
    ∀ {X : Scheme.{u}} [ConnectedSpace X]
      {xbar xbar' : GeometricPoint X}
      (t : GeometricPoint.finiteFiber xbar ≅ GeometricPoint.finiteFiber xbar'),
      Nonempty (CatCommSq (𝟭 (FiniteEtale X))
        (GeometricPoint.fiberAction xbar') (GeometricPoint.fiberAction xbar)
        (ContAction.res FintypeCat (GeometricPoint.autHom t))))
