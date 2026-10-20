/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) S.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) S.smallEtaleTopology X.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- If `f : X ⟶ S` is a smooth proper morphism of schemes,
`Λ` is a Noetherian ring, and `F` is a finite-type locally constant sheaf of
`Λ`-modules on the small étale site of `X` such that for every geometric point
`xbar` of `X` the stalk `étaleModuleStalk xbar F` is annihilated by an integer
`n > 0` prime to the residue characteristic of `xbar`, then for all `i : ℤ`
the homology sheaf of `etaleDerivedPushforward f` applied to `F` placed in
degree `0` is a finite-type locally constant sheaf of `Λ`-modules on the small
étale site of `S`. -/
@[stacks 0GLI]
theorem etaleDerivedPushforward_homology_isFiniteTypeLocallyConstantModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (h_stalk : ∀ xbar : GeometricPoint X,
      ∃ n : ℕ, 0 < n ∧
        Module.IsTorsionBy Λ (étaleModuleStalk xbar F) (n : Λ) ∧
        (n : xbar.K) ≠ 0)
    (i : ℤ) :
    Sheaf.IsFiniteTypeLocallyConstantModule
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) i).obj
        ((etaleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  sorry

/-- The higher direct images of a finite-type locally constant étale module sheaf
under a smooth proper morphism are finite-type locally constant when every geometric
stalk is killed by a positive integer prime to its residue characteristic, with
the stalk condition supplied as a `Fact` instance. -/
instance etaleDerivedPushforward.homology_isFiniteTypeLocallyConstantModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    [Fact (∀ xbar : GeometricPoint X,
      ∃ n : ℕ, 0 < n ∧
        Module.IsTorsionBy Λ (étaleModuleStalk xbar F) (n : Λ) ∧
        (n : xbar.K) ≠ 0)]
    (i : ℤ) :
    Sheaf.IsFiniteTypeLocallyConstantModule
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) i).obj
        ((etaleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  etaleDerivedPushforward_homology_isFiniteTypeLocallyConstantModule f F Fact.out i

end AlgebraicGeometry.Scheme.Etale

end
