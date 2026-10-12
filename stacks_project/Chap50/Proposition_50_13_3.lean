/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch.Absolute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham
open AlgebraicGeometry.Scheme.DeRham.LerayHirsch
open scoped MonoidalCategory TensorProduct

universe u

/- Proposition 50.13.3 (1): absolute de Rham classes forming a basis on every residue fiber
give an isomorphism from the finite biproduct of negatively shifted de Rham complexes to the
derived pushforward. -/
@[stacks 0FMR] #check (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.overBaseMap_isIso :
  ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}
    (sq : CommSq f a b (𝟙 S))
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [Smooth f] [IsProper f]
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom
        (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ))
    (hξ : IsAbsoluteFiberwiseBasis sq n ξ),
    IsIso (overBaseMap sq n ξ))

/- Proposition 50.13.3 (2): in every degree, the cup-product map from the shifted de Rham
cohomology of `Y/S` to the scalar-restricted de Rham cohomology of `X/S` is an isomorphism. -/
@[stacks 0FMR] #check (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.overBaseCohomologyMap_isIso :
  ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}
    (sq : CommSq f a b (𝟙 S))
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [Smooth f] [IsProper f]
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom
        (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ))
    (hξ : IsAbsoluteFiberwiseBasis sq n ξ),
    ∀ q : ℤ, IsIso (overBaseCohomologyMap sq n ξ q))
