/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent.Derived
import StacksCheckRecall

/-!
# Lemma 85.25.3

For a proper hypercovering of a Hausdorff locally compact space, the canonical
unit `K ⟶ Ra_* (a⁻¹ K)` is an isomorphism for every `K` in `D⁺(X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject

universe u

/- Lemma 85.25.3. For an augmentation giving a proper hypercovering, the canonical
bounded-below derived unit of its Zariski augmentation is an isomorphism. -/
@[stacks 09XS] #check (LCCat.plusDerivedUnit_app_isIso :
  ∀ {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
    [HasSheafify (zariskiTopology (LCCat.forgetToTop.obj U)) AddCommGrpCat.{u}]
    [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
    [(augmentationPushforward (LCCat.toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology (LCCat.forgetToTop.obj U)) AddCommGrpCat.{u}))]
    (ha : LCCat.IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})),
    IsIso ((plusDerivedUnit (LCCat.toTopCatAugmentation a)).app K))

#check (LCCat.plusDerivedUnit_isIso :
  ∀ {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
    [HasSheafify (zariskiTopology (LCCat.forgetToTop.obj U)) AddCommGrpCat.{u}]
    [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
    [(augmentationPushforward (LCCat.toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology (LCCat.forgetToTop.obj U)) AddCommGrpCat.{u}))]
    (ha : LCCat.IsProperHypercovering a),
    IsIso (plusDerivedUnit (LCCat.toTopCatAugmentation a)))
