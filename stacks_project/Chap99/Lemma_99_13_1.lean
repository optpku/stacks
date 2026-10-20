module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import stacks_project.Chap99.Lemma_99_13_1_Spaces
import StacksCheckRecall

/-!
# Lemma 99.13.1

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` are fibered
in groupoids over `(Sch/S)_fppf`.
-/

universe u

/- Lemma 99.13.1 (1): finite-type algebraic spaces with cartesian squares as
morphisms form a category fibred in groupoids. -/
@[stacks 0D1E]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FtGroupoids.instIsFiberedInGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.Functor.IsFibered.InGroupoids
    (AlgebraicGeometry.AlgebraicSpace.Spaces.pFtGroupoids S))

/- Lemma 99.13.1 (2): the finite-presentation, flat, proper full subcategory
is fibred in groupoids. -/
@[stacks 0D1E]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.instIsFiberedInGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.Functor.IsFibered.InGroupoids
    (AlgebraicGeometry.AlgebraicSpace.Spaces.pFpFlatProperGroupoids S))

