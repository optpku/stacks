/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiniteLocallyFree
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 40.14.2: A groupoid scheme with finite source and target maps admits an invariant
open subscheme and an invariant closed thickening whose closure meets every orbit and whose
restricted source and target maps are finite locally free. -/
@[stacks 0ABA] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantOpenThickening :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [IsFinite G.s.left] [IsFinite G.t.left],
      ∃ (W : Scheme.Opens G.U.left) (Z : Scheme.IdealSheafData (W : Scheme)),
        let i : Over.mk ((Z.subschemeι ≫ W.ι) ≫ G.U.hom) ⟶ G.U :=
          Over.homMk (Z.subschemeι ≫ W.ι)
        G.toPreRelation.IsOpenInvariant W ∧
          G.toPreRelation.IsInvariant (Subobject.mk (Z.subschemeι ≫ W.ι)) ∧
            G.t.left '' (G.s.left ⁻¹' closure (W : Set G.U.left)) = Set.univ ∧
              IsThickening Z.subschemeι ∧
                IsFiniteLocallyFree (G.pullback i).s.left ∧
                  IsFiniteLocallyFree (G.pullback i).t.left)
