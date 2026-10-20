/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.ZeroScheme
public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The Gysin bivariant class of the zero scheme of a section of an invertible module
equals the degree-one virtual-normal class associated to the pulled-back module. -/
theorem gysin_eq_ofZeroScheme
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (D : ClosedDeformation (zeroSchemeι ℒ s ≫ X.hom) X.hom
      (zeroSchemeι ℒ s) rfl (ofZeroScheme ℒ s)) :
    BivariantClass.gysin δ X ℒ s =
      globalClassOfRank δ (zeroSchemeι ℒ s ≫ X.hom) X.hom (zeroSchemeι ℒ s) rfl
        (ofZeroScheme ℒ s) D 1 := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
