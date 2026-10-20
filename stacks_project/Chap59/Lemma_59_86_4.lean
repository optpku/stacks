/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.DerivedInverseSystem
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.BaseChange

universe u

/- Lemma 59.86.4: for a directed inverse system of cartesian étale squares,
stagewise canonical derived base-change isomorphisms imply the corresponding
isomorphism for the limit square after pulling back a bounded-below coefficient
from a chosen stage. -/
@[stacks 0GJL] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedBaseChange_of_inverseSystem_plus :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (C : InverseSystemCartesianSquare I)
      [∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap C.DX hij)]
      [∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap C.DY hij)]
      [∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap C.DS hij)]
      [∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap C.DT hij)]
      [∀ i : I, QuasiCompact (C.g i)]
      [∀ i : I, QuasiSeparated (C.g i)]
      [QuasiCompact C.gLim] [QuasiSeparated C.gLim]
      (i0 : I)
      (K0 : DerivedCategory.Plus
        (Sheaf (C.DT.obj (OrderDual.toDual i0)).smallEtaleTopology
          AddCommGrpCat.{u + 1}))
      (h_stage : ∀ (i : I) (hi : i0 ≤ i),
        IsIso (derivedMap (C.f i) (C.h i) (C.e i) (C.g i) (C.stage_isPullback i)
          (stagePlusPullback C i0 i hi K0)))
      , IsIso (derivedMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback
        (limitPlusPullback C i0 K0)))
