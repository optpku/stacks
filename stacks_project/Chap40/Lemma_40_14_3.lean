/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FinitePresentation
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

universe u

/- Lemma 40.14.3: If the source and target maps of a groupoid scheme are finite and of finite
presentation, the invariant open thickening can be chosen with a finitely presented closed
immersion, and every point whose orbit consists of generic points belongs to that open. -/
@[stacks 0ABB] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantOpenThickening_of_finitePresentation :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [IsFinite G.s.left] [IsFinite G.t.left]
      [Scheme.Hom.FinitePresentation G.s.left]
      [Scheme.Hom.FinitePresentation G.t.left],
      ∃ (W : Scheme.Opens G.U.left) (Z : Scheme.IdealSheafData (W : Scheme)),
        let i : Over.mk ((Z.subschemeι ≫ W.ι) ≫ G.U.hom) ⟶ G.U :=
          Over.homMk (Z.subschemeι ≫ W.ι)
        G.toPreRelation.IsOpenInvariant W ∧
          G.toPreRelation.IsInvariant (Subobject.mk (Z.subschemeι ≫ W.ι)) ∧
            G.t.left '' (G.s.left ⁻¹' closure (W : Set G.U.left)) = Set.univ ∧
              IsThickening Z.subschemeι ∧
                Scheme.Hom.FinitePresentation Z.subschemeι ∧
                  IsFiniteLocallyFree (G.pullback i).s.left ∧
                    IsFiniteLocallyFree (G.pullback i).t.left ∧
                      ∀ u : G.U.left,
                        G.t.left '' (G.s.left ⁻¹' {u}) ⊆ genericPoints G.U.left → u ∈ W)
