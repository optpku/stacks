/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.EllTorsion
public import ReasLib.CategoryTheory.Sites.ModuleCat.Forget
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- The underlying abelian étale sheaf of a sheaf of modules over any modulus. -/
def modSheafToAbelian {X : Scheme.{u}} {modulus : ℕ}
    (sheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod modulus))) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (moduleSheafToAddCommGrp X.smallEtaleTopology (ZMod modulus)).obj sheaf

/-- Torsion étale cohomology commutes with base change when every canonical
higher-direct-image comparison associated to a cartesian square is invertible. -/
def CohomologyCommutesWithBaseChange (f : X ⟶ Y) : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      IsLocallyTorsion sheaf →
      ∀ degree : ℕ, IsIso (higherDirectImageBaseChange f g f' g' h_cart sheaf degree)

/-- Commutation with base change makes the comparison for any torsion sheaf
and any cohomological degree an isomorphism. -/
theorem cohomologyCommutesWithBaseChange_apply {f : X ⟶ Y}
    (h : CohomologyCommutesWithBaseChange f)
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h_cart : IsPullback g' f' f g)
    {sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (hSheaf : IsLocallyTorsion sheaf)
    (degree : ℕ) :
    IsIso (higherDirectImageBaseChange f g f' g' h_cart sheaf degree) :=
  h g f' g' h_cart sheaf hSheaf degree

/-- Positive higher direct images of pulled-back injective prime-modulus
module sheaves vanish after every cartesian base change. -/
def injectiveMod_higherDirectImage_isZero (f : X ⟶ Y) : Prop :=
  ∀ (modulus : ℕ), Nat.Prime modulus →
    ∀ (sheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod modulus))),
      Injective sheaf →
      ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
        IsPullback g' f' f g →
        ∀ degree : ℕ, 0 < degree →
          IsZero (schemeHigherDirectImage f'
            (abelianPullbackAlong g' (modSheafToAbelian sheaf)) degree)

/-- The injective-coefficient vanishing condition implies vanishing for each
injective prime-modulus module sheaf, cartesian square, and positive degree. -/
theorem injectiveMod_higherDirectImage_isZero_apply {f : X ⟶ Y}
    (h : injectiveMod_higherDirectImage_isZero f)
    {modulus : ℕ} (hPrime : Nat.Prime modulus)
    {sheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod modulus))}
    (hInjective : Injective sheaf)
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h_cart : IsPullback g' f' f g) {degree : ℕ} (hPositive : 0 < degree) :
    IsZero (schemeHigherDirectImage f'
      (abelianPullbackAlong g' (modSheafToAbelian sheaf)) degree) :=
  h modulus hPrime sheaf hInjective g f' g' h_cart degree hPositive

/-- For a proper morphism, torsion étale cohomology commutes with arbitrary
base change precisely when inverse images of injective prime-modulus module
sheaves have vanishing positive higher direct images. -/
theorem cohomologyCommutesWithBaseChange_iff (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange f ↔ injectiveMod_higherDirectImage_isZero f := sorry

end AlgebraicGeometry.Scheme.Hom

end
