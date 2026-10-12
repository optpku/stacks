/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finite-presentation groupoid schemes

This module records the finite-presentation refinement of the invariant open-thickening
construction for finite groupoid schemes.
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme with finite and finitely presented source and target maps admits an
invariant open subscheme and an invariant closed thickening whose closure meets every orbit,
whose closed immersion is finitely presented, and whose restricted source and target maps are
finite locally free. Every point whose entire orbit consists of generic points belongs to the
chosen open subscheme. -/
theorem exists_invariantOpenThickening_of_finitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
    [Scheme.Hom.FinitePresentation G.s.left]
    [Scheme.Hom.FinitePresentation G.t.left] :
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
                      G.t.left '' (G.s.left ⁻¹' {u}) ⊆ genericPoints G.U.left → u ∈ W := sorry

end AlgebraicGeometry.GroupoidScheme
