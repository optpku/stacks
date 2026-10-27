/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Cochain
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.HomologyZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.NaiveComparison

/-!
# Low-degree Ext comparisons for ringed-space cotangent complexes

Truncation identifies Ext¹ of the naive and full cotangent complexes, and
augmentation identifies degree-zero Ext with morphisms from relative differentials.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace.Cotangent

variable {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules)

/-- Derived morphism `L[f] ⟶ NL[f]` in `D(𝒪_X)`. -/
def toNaiveDerived : derived f ⟶ (DerivedCategory.Q (C := X.Modules)).obj NL[f] :=
  (DerivedCategory.Q (C := X.Modules)).map (toNaive f)

/-- Unfolding of `toNaiveDerived` as `Q.map` of `toNaive`. -/
theorem toNaiveDerived_eq :
    toNaiveDerived f = (DerivedCategory.Q (C := X.Modules)).map (toNaive f) :=
  rfl

/-- Section `NL[f] ⟶ τ_{≥ -1} L[f]` in `D(𝒪_X)`, via `πTruncGE`, the truncation
quasi-isomorphism of `toNaive`, and the canonical `qHom` comparison. -/
def toTruncGESection :
    (DerivedCategory.Q (C := X.Modules)).obj NL[f] ⟶ (DerivedCategory.TStructure.t.truncGE (-1)).obj (derived f) :=
  (DerivedCategory.Q (C := X.Modules)).map ((naiveCotangent f).πTruncGE (-1)) ≫
    inv ((DerivedCategory.Q (C := X.Modules)).map (CochainComplex.truncGEMap (toNaive f) (-1))) ≫
    inv (DerivedCategory.TruncGE.qHom (A := X.Modules) (cotangentComplex f) (-1))

/-- The shifted coefficient object `G[1]` lies in `t.GE (-1)`. -/
instance coeffSingle_shift_isGE :
    DerivedCategory.TStructure.t.IsGE (((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift ((DerivedCategory.singleFunctor X.Modules 0).obj G) (0 : ℤ) (1 : ℤ) (-1)

/-- The Ext¹ class of `NL[f]` obtained from a derived Ext¹ class by `descTruncGE`
and `toTruncGESection`. -/
def fromDerivedToNaiveExt (η : Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f], (DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toTruncGESection f))
    (DerivedCategory.TStructure.t.descTruncGE (η : derived f ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧) (-1))
    (add_zero (1 : ℤ))

/-- The additive identification of Ext¹ of the naive and full cotangent complexes. -/
def extOneTruncEquiv :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f], (DerivedCategory.singleFunctor X.Modules 0).obj G) ≃+
      Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) where
  toFun ξ :=
    ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ (add_zero (1 : ℤ))
  invFun η := fromDerivedToNaiveExt f G η
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `extOneTruncEquiv` is precomposition along `toNaiveDerived`. -/
theorem extOneTruncEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f], (DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    extOneTruncEquiv f G ξ =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ
        (add_zero (1 : ℤ)) :=
  rfl

/-- The unshifted morphism `L[f] ⟶ G[0]` attached to a map out of `Ω[f]`. -/
def homKaehlerDerived (α : Ω[f] ⟶ G) : derived f ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj G :=
  (DerivedCategory.Q (C := X.Modules)).map
    (CotangentComplex.augmentation (inverseImageStructureSheafHomComm f) ≫
      (CochainComplex.singleFunctor X.Modules 0).map α)

/-- The Hom representative of an Ext⁰ class, obtained from `H^0` along `homologyZeroIso`. -/
def homOfExtZero (e : Ext⁽(0 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G)) : Ω[f] ⟶ G :=
  (homologyZeroIso f).inv ≫
    (DerivedCategory.homologyFunctorFactors X.Modules (0 : ℤ)).inv.app (cotangentComplex f) ≫
    (DerivedCategory.homologyFunctor X.Modules (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors X.Modules (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor X.Modules 0).obj G) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) G).hom

/-- The Ext⁰ identification `Hom(Ω[f], G) ≃ Ext⁽0⁾(Q L[f], Q(G[0]))`. -/
def extZeroHomEquiv : (Ω[f] ⟶ G) ≃ Ext⁽(0 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α)
  invFun e := homOfExtZero f G e
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω[f] ⟶ G) :
    extZeroHomEquiv f G α = ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α) :=
  rfl

end AlgebraicGeometry.RingedSpace.Cotangent
