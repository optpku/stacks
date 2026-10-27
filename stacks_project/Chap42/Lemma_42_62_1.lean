/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Over
public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.ChowGroup.Total

noncomputable section

universe u

variable {k : Type u} [Field k]

/- Lemma 42.62.1. Intersection products over a smooth scheme over a field are associative,
including when the dimensions of its open-and-closed components vary. The explicit datum D
is a chosen model of deformation to the normal cone of the diagonal; canonical production
of this model is a library follow-up. -/
@[stacks 0FC1] #check (AlgebraicGeometry.ChowGroup.Total.intersectionProductOver_assocOfRankLoci :
  ∀
    (X : SchemeOverField k) [Smooth X.hom] {Y Z W : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] [LocallyOfFiniteType fW.left]
    (D : DiagonalSpecializationOfRankLoci X)
    (alpha : Total (fun _ ↦ 0) Y) (beta : Total (fun _ ↦ 0) Z)
    (gamma : Total (fun _ ↦ 0) W),
    map (fun _ ↦ 0) (pullbackAssoc fY fZ fZ fW).hom
        (intersectionProductOverOfRankLoci X (pullback.snd fY fZ ≫ fZ) fW D
          (intersectionProductOverOfRankLoci X fY fZ D alpha beta) gamma) =
      intersectionProductOverOfRankLoci X fY (pullback.fst fZ fW ≫ fZ) D alpha
        (intersectionProductOverOfRankLoci X fZ fW D beta gamma))
