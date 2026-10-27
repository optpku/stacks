/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Automorphisms
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Fiber
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Torsor

/-!
# Cotangent obstruction and classification of first-order solutions

The full cotangent complex controls existence, translation of compatible
isomorphism classes, and compatible automorphisms of first-order deformations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/-- The tautological Ext¹ class of `t` after derived pullback along `f` and the coefficient
map `c`. -/
def xiPrimeNaive :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived f).obj ((DerivedCategory.Q (C := S.Modules)).obj NL[t]), (DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  extOne_map (cPull t f c) (selfExtensionClass t)

/-- `xiPrimeNaive` is `extOne_map` of `selfExtensionClass t` along `cPull t f c`. -/
theorem xiPrimeNaive_eq :
    xiPrimeNaive t f G c = extOne_map (cPull t f c) (selfExtensionClass t) :=
  rfl

/-- The pulled-back tautological class is postcomposed with the prescribed coefficient map. -/
theorem xiPrimeNaive_spec :
    xiPrimeNaive t f G c = extOne_postcomp (cPull t f c) (extOne_pullback f (selfExtensionClass t)) :=
  rfl

/-- The canonical map from the coefficient-tower cotangent object to the derived
pullback of the naive cotangent complex. -/
def toPullbackNaive :
    pullbackCotangent f t ⟶
      (modulePullbackDerived f).obj ((DerivedCategory.Q (C := S.Modules)).obj NL[t]) :=
  (pullbackCotangentIso f t).hom ≫
    (modulePullbackDerived f).map (Cotangent.toNaiveDerived t)

/-- The comparison is derived pullback of the canonical cotangent comparison,
preceded by the coefficient-tower identification. -/
theorem toPullbackNaive_eq :
    toPullbackNaive t f =
      (pullbackCotangentIso f t).hom ≫
        (modulePullbackDerived f).map (Cotangent.toNaiveDerived t) := rfl

/-- The canonical Ext¹ class ξ' of `Lf^* L[t]` with coefficients `G`. -/
def xiPrime :
    Ext⁽(1 : ℤ)⁾(pullbackCotangent f t, (DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
    (xiPrimeNaive t f G c) (add_zero (1 : ℤ))

/-- `xiPrime` is precomposition of `xiPrimeNaive` along `toPullbackNaive`. -/
theorem xiPrime_eq :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (xiPrimeNaive t f G c) (add_zero (1 : ℤ)) :=
  rfl

/-- The full cotangent class is the pulled-back tautological class precomposed
with the canonical comparison to the naive cotangent complex. -/
theorem xiPrime_spec :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (extOne_map (cPull t f c) (selfExtensionClass t)) (add_zero (1 : ℤ)) :=
  rfl

/-- The canonical Ext² existence obstruction of the first-order deformation equation. -/
def existenceObstruction :
    Ext⁽(2 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  ShiftedHom.comp (connectingMap f t) (xiPrime t f G c) rfl

/-- `existenceObstruction` is `ShiftedHom.comp` of `connectingMap` with `xiPrime`. -/
theorem existenceObstruction_eq :
    existenceObstruction t f G c =
      ShiftedHom.comp (connectingMap f t) (xiPrime t f G c) rfl :=
  rfl

/-- `existenceObstruction` is the connecting image of the tautological class of `t` along `c`. -/
theorem existenceObstruction_spec :
    existenceObstruction t f G c =
      ShiftedHom.comp (connectingMap f t)
        (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
          (xiPrimeNaive t f G c) (add_zero (1 : ℤ))) rfl :=
  rfl

namespace Solution

/-- Derived Ext¹ translates solution classes by transport of naive cotangent translation. -/
def derivedVadd (ξ : Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G))
    (p : IsoClass t f G c) : IsoClass t f G c :=
  Solution.vadd ((Cotangent.extOneTruncEquiv f G).symm ξ) p

/-- The difference of two solution classes is their naive difference transported to derived Ext¹. -/
def derivedVsub (p q : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  Cotangent.extOneTruncEquiv f G (Solution.vsub p q)

/-- Translation by the zero derived Ext¹ class fixes every solution class. -/
theorem derivedVadd_zero (p : IsoClass t f G c) :
    derivedVadd t f G c 0 p = p := sorry

/-- Derived Ext¹ translation respects addition. -/
theorem derivedVadd_add
    (ξ η : Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G))
    (p : IsoClass t f G c) :
    derivedVadd t f G c (ξ + η) p =
      derivedVadd t f G c ξ (derivedVadd t f G c η p) := sorry

/-- Translating the second class by its difference from the first recovers the first class. -/
theorem derivedVsub_vadd (p q : IsoClass t f G c) :
    derivedVadd t f G c (derivedVsub t f G c p q) q = p := sorry

/-- The difference of a translate from its base class is the translation parameter. -/
theorem derivedVadd_vsub
    (ξ : Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G))
    (p : IsoClass t f G c) :
    derivedVsub t f G c (derivedVadd t f G c ξ p) p = ξ := sorry

/-- A solution supplies nonemptiness for the additive torsor of solution classes under derived Ext¹. -/
@[reducible]
def derivedAddTorsor (S0 : Solution t f G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G))
      (IsoClass t f G c) where
  vadd := derivedVadd t f G c
  vsub := derivedVsub t f G c
  zero_vadd := derivedVadd_zero t f G c
  add_vadd := derivedVadd_add t f G c
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := derivedVsub_vadd t f G c
  vadd_vsub' := derivedVadd_vsub t f G c

end Solution

/-- The canonical Ext² obstruction vanishes exactly when a compatible solution exists. -/
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction t f G c = 0 ↔ Nonempty (Solution t f G c) :=
  sorry

/-- A base solution identifies derived Ext¹ with compatible isomorphism classes of solutions. -/
def isoClassDerivedEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) ≃ IsoClass t f G c :=
  (Cotangent.extOneTruncEquiv f G).symm.toEquiv.trans (isoClassEquiv S0)

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    isoClassDerivedEquiv t f G c S0 ξ =
      isoClassEquiv S0 ((Cotangent.extOneTruncEquiv f G).symm ξ) :=
  rfl

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : Solution t f G c) :
    isoClassDerivedEquiv t f G c S0 0 = isoClassMk S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`Cotangent.extOneTruncEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : Solution t f G c)
    (p : IsoClass t f G c) :
    (isoClassDerivedEquiv t f G c S0).symm p =
      Cotangent.extOneTruncEquiv f G ((isoClassEquiv S0).symm p) :=
  rfl

/-- Derived Ext⁰ is canonically equivalent to the compatible automorphisms of a solution. -/
def autEquiv (S : Solution t f G c) :
    Ext⁽(0 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) ≃ Solution.Fitting S S where
  toFun e :=
    Solution.Fitting.perturb (idFitting t f G c S)
      (homToPerturb t f G c S ((Cotangent.extZeroHomEquiv f G).symm e))
  invFun φ :=
    Cotangent.extZeroHomEquiv f G (perturbToHom t f G c S (Solution.Fitting.diff (idFitting t f G c S) φ))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idFitting`. -/
theorem autEquiv_apply (S : Solution t f G c)
    (e : Ext⁽(0 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    autEquiv t f G c S e =
      Solution.Fitting.perturb (idFitting t f G c S)
        (homToPerturb t f G c S ((Cotangent.extZeroHomEquiv f G).symm e)) :=
  rfl

end AlgebraicGeometry.RingedSpace.Thickening
