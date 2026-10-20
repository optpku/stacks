/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity

universe u

/- Lemma 42.54.10: Compatible virtual normal bundles for nested closed immersions
satisfy the completed Gysin composition identity in every nonnegative degree. -/
@[stacks 0FEC] #check
  (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_comp :
    ∀ {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V : VirtualNormalBundle (i ≫ j))
    (D : ClosedDeformation (i ≫ j ≫ p) p (i ≫ j) rfl V)
    (V' : VirtualNormalBundle i)
    (D' : ClosedDeformation (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedDeformation (j ≫ p) p j rfl V'')
    (incl :
      (Scheme.Modules.pullback i).obj (Scheme.Modules.dual V''.module) ⟶
        Scheme.Modules.dual V.module)
    (proj : Scheme.Modules.dual V.module ⟶ Scheme.Modules.dual V'.module)
    (hzero : incl ≫ proj = 0) (hshort : (ShortComplex.mk incl proj hzero).ShortExact)
    (h_left :
      CommSq incl ((Scheme.Modules.pullback i).map V''.map) V.map
        (baseChange i j))
    (h_right :
      CommSq proj V.map V'.map (projection i j))
    (n : ℕ),
    globalClassOfRank delta (i ≫ j ≫ p) p (i ≫ j) rfl V D n =
      globalClassConvolution delta p j i V' D' V'' D'' n)
