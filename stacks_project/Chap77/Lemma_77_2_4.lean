/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Impurity.Ascent
import StacksCheckRecall

/-!
# Flat ascent of impurities

A morphism of pointed algebraic spaces that is flat at the selected point lifts
an impurity of a finite-type quasi-coherent module to an impurity of the
pullback, étale over the original base-change scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.2.4: impurities ascend along pointed morphisms flat at the selected
point, with the new impurity scheme étale over the base change of the original. -/
@[stacks 0CVA] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Impurity.exists_of_flatAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (φ : Y1 ⟶ Y) {y1 : Points Y1}
    (h_map : Points.map φ y1 = y) (h_flat : FlatAt φ y1)
    (I : Impurity F f y),
    ∃ (I1 : Impurity ((Modules.pullback (Limits.pullback.fst f φ)).obj F)
        (Limits.pullback.snd f φ) y1)
      (π : ofOver I1.T ⟶ Limits.pullback φ I.g),
      AlgebraicSpace.Etale π ∧ I1.g = π ≫ Limits.pullback.fst φ I.g)
