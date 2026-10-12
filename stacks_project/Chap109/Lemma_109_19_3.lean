/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Relative dualizing sheaf of a Gorenstein family of curves

For a family of curves with Gorenstein fibres equidimensional of dimension 1,
the degree `-1` cohomology sheaf of a relative dualizing complex is an
invertible `𝒪_X`-module, and its formation commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- Lemma 109.19.3 (1): for a family of curves `f : X ⟶ Y` with Gorenstein fibres
equidimensional of dimension 1, the relative dualizing sheaf
`cohomologySheaf C.complex (-1)` is an invertible `𝒪_X`-module. -/
@[stacks 0E6R]
instance instIsInvertibleObject_cohomologySheaf {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f) :
    isInvertibleObject (cohomologySheaf C.complex (-1)) :=
  sorry

/-- Lemma 109.19.3 (2): formation of the relative dualizing sheaf of a Gorenstein
family of curves of relative dimension 1 commutes with arbitrary base change. -/
@[stacks 0E6R]
theorem cohomologySheaf_baseChange_of_gorenstein {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f)
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsFamily f'] [Gorenstein f'] [RelativeDimension f' 1]
    (sq : IsPullback g' f' f g) (C' : RelativeDualizingComplex f') :
    IsIsomorphic
      ((Modules.pullback g').obj (cohomologySheaf C.complex (-1)))
      (cohomologySheaf C'.complex (-1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
