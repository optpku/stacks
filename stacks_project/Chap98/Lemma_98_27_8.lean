module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap98.Lemma_98_27_6_Solution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed-immersion solutions of Artin contractions

In Situation 98.27.1, a closed subset `Z ⊂ S` whose inverse image in `X'` is
`T'`, with `U' ⟶ S \ Z` and `W ⟶ S_/Z` closed immersions, yields a solution
whose structure morphism `X ⟶ S` is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

/-- The structure map `|X| ⟶ S` is continuous. -/
theorem continuous_base {S : Scheme.{u}} {X : AlgebraicSpace S} :
    Continuous (base : Points X → S) :=
  sorry

end Points

namespace ofOver

/-- Transport a closed subset `Z ⊂ S` along `pointsEquiv` to a closed subset of
`Points (ofOver (Over.mk (𝟙 S)))`. -/
def pointsCloseds {S : Scheme.{u}} (Z : Closeds S) :
    Closeds (Points (ofOver (Over.mk (𝟙 S)))) where
  carrier := Set.image (pointsEquiv (Over.mk (𝟙 S))) (Z : Set S)
  isClosed' :=
    (pointsHomeomorph (Over.mk (𝟙 S))).isClosedMap (Z : Set S) Z.isClosed

/-- A point of `ofOver (Over.mk (𝟙 S))` lies in `pointsCloseds Z` if and only if
it is the image of a point of `Z`. -/
theorem mem_pointsCloseds {S : Scheme.{u}} {Z : Closeds S}
    {x : Points (ofOver (Over.mk (𝟙 S)))} :
    x ∈ pointsCloseds Z ↔
      ∃ z ∈ Z, pointsEquiv (Over.mk (𝟙 S)) z = x :=
  sorry

/-- Preimage of `pointsCloseds Z` along `|X| ⟶ |S|` recovers the preimage of
`Z` along `Points.base`. -/
theorem pointsCloseds_preimage_toBase {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : Closeds S) :
    (pointsCloseds Z).preimage (Points.continuous_map (toBase X)) =
      Z.preimage Points.continuous_base :=
  sorry

end ofOver

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.8: In Situation 98.27.1, given a closed subset `Z ⊂ S` whose
inverse image in `X'` is `T'`, such that `U' ⟶ S \ Z` and `W ⟶ S_/Z` are
closed immersions, there exists a solution `(f : X' ⟶ X, T, a)`, and moreover
`X ⟶ S` is a closed immersion.

Here `S \ Z` is identified with
`openComplementAlong (ofOver (Over.mk (𝟙 S))) (ofOver.pointsCloseds Z)` and
`S_/Z` with
`completionAlong (ofOver (Over.mk (𝟙 S))) (ofOver.pointsCloseds Z)`. The
morphism `U' ⟶ S \ Z` is
`openComplementAlong.map (toBase σ.X') (ofOver.pointsCloseds Z)`. -/
@[stacks 0GHE]
theorem exists_solutionFor_of_closedImmersions
    (σ : ContractionSituation S) (Z : Closeds S)
    (h_inv : σ.T' = (ofOver.pointsCloseds Z).preimage
      (Points.continuous_map (toBase σ.X')))
    [IsClosedImmersion
      (openComplementAlong.map (toBase σ.X') (ofOver.pointsCloseds Z))]
    (w : σ.W ⟶
      completionAlong (ofOver (Over.mk (𝟙 S))) (ofOver.pointsCloseds Z))
    [FormalAlgebraicSpace.ClosedImmersion w] :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X) ∧ IsClosedImmersion (toBase X) :=
  sorry

/-- Unpacking of `exists_solutionFor_of_closedImmersions`: there is an algebraic
space `X` locally of finite type over `S`, a solution `sol : SolutionFor σ X`,
and a closed immersion `X ⟶ S`. -/
theorem exists_solutionFor_of_closedImmersions_spec
    (σ : ContractionSituation S) (Z : Closeds S)
    (h_inv : σ.T' = (ofOver.pointsCloseds Z).preimage
      (Points.continuous_map (toBase σ.X')))
    [IsClosedImmersion
      (openComplementAlong.map (toBase σ.X') (ofOver.pointsCloseds Z))]
    (w : σ.W ⟶
      completionAlong (ofOver (Over.mk (𝟙 S))) (ofOver.pointsCloseds Z))
    [FormalAlgebraicSpace.ClosedImmersion w] :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X))
      (sol : SolutionFor σ X), IsClosedImmersion (toBase X) :=
  sorry

/-- If a closed subspace `X ⊂ S` interpolates `U'` on `S \ Z` and matches `w`
on completions, then `X` is a solution. -/
theorem nonempty_solutionFor_of_interpolatingClosedSubspace
    (σ : ContractionSituation S) (Z : Closeds S)
    (h_inv : σ.T' = (ofOver.pointsCloseds Z).preimage
      (Points.continuous_map (toBase σ.X')))
    (X : ClosedSubspace (ofOver (Over.mk (𝟙 S))))
    [LocallyOfFiniteType (toBase X.X)]
    (e_open :
      openComplementAlong σ.X'
          ((ofOver.pointsCloseds Z).preimage
            (Points.continuous_map (toBase σ.X'))) ≅
        openComplementAlong X.X
          ((ofOver.pointsCloseds Z).preimage (Points.continuous_map X.ι)))
    (h_open :
      e_open.hom ≫ openComplementAlong.map X.ι (ofOver.pointsCloseds Z) =
        openComplementAlong.map (toBase σ.X') (ofOver.pointsCloseds Z))
    (w : σ.W ⟶
      completionAlong (ofOver (Over.mk (𝟙 S))) (ofOver.pointsCloseds Z))
    (e_hat :
      completionAlong X.X
          ((ofOver.pointsCloseds Z).preimage (Points.continuous_map X.ι)) ≅
        σ.W)
    (h_hat :
      e_hat.inv ≫ completionAlong.map X.ι (ofOver.pointsCloseds Z) = w) :
    Nonempty (SolutionFor σ X.X) :=
  sorry

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
