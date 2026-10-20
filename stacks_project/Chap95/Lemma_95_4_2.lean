module

public import ReasLib.AlgebraicGeometry.QCohStack.Stack
import StacksCheckRecall

/-!
# Lemma 95.4.2

The functor `p : QCohStack ⥤ (Sch/S)_fppf` satisfies conditions (1), (2) and
(3) of Stacks Definition 8.4.1: it is fibered, Hom-presheaves of restrictions
are sheaves, and descent data for fppf coverings are effective.
-/

universe u

/- Lemma 95.4.2: the functor `p : QCohStack ⥤ (Sch/S)_fppf` satisfies
conditions (1), (2) and (3) of Stacks Definition 8.4.1. -/
@[stacks 03YM] #check (AlgebraicGeometry.QCohStack.instIsStackOnSite :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    CategoryTheory.IsStack.OnSite (AlgebraicGeometry.Scheme.fppfTopology.over S)
      (AlgebraicGeometry.QCohStack.p S))
