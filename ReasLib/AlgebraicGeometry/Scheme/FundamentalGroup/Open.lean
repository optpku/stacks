/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Galois.Action

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
universe u w

namespace AlgebraicGeometry.Scheme

/-- A homomorphism compatible with finite étale base change from a nonempty
open of an irreducible geometrically unibranch scheme is surjective. -/
theorem fundamentalGroupMap_surjective_of_openBaseChangeSquare
    {X : Scheme.{u}} [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (U : X.Opens) (hU : (U : Set X).Nonempty)
    (FX : FiniteEtale X ⥤ FintypeCat.{w})
    [GaloisCategory (FiniteEtale X)] [FiberFunctor FX]
    (FU : FiniteEtale (U : Scheme) ⥤ FintypeCat.{w})
    [GaloisCategory (FiniteEtale (U : Scheme))] [FiberFunctor FU]
    (h : ContinuousMonoidHom (Aut FU) (Aut FX))
    (sq : CatCommSq (finiteEtaleBaseChange U.ι) (functorToAction FX)
      (functorToAction FU) (Action.res FintypeCat h.toMonoidHom)) :
    Function.Surjective h := sorry

/-- The inclusion of a nonempty open in an irreducible geometrically
unibranch scheme induces a surjection on fundamental groups at any
geometric point of the open. -/
theorem fundamentalGroupMap_surjective_of_nonemptyOpen
    {X : Scheme.{u}} [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (U : X.Opens) (hU : (U : Set X).Nonempty)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ (U : Scheme)) :
    Function.Surjective (Hom.fundamentalGroupMap U.ι s) := sorry

end AlgebraicGeometry.Scheme
