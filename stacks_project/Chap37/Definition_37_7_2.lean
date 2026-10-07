module

import stacks_project.Chap37.Lemma_37_7_1
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.FormallyUnramified.existsUniversalFirstOrderThickening :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (h : Z ⟶ X)
      [AlgebraicGeometry.FormallyUnramified h],
      ∃ T : AlgebraicGeometry.Thickening.Over X,
        T.left = Over.mk h ∧ AlgebraicGeometry.Thickening.IsUniversalFirstOrder T)

/- Definition 37.7.2: the conormal sheaf of a formally unramified morphism is the conormal
sheaf of its source in an explicit universal first-order thickening. -/
@[stacks 04F4] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalSheaf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.Thickening.Over X)
      [AlgebraicGeometry.FormallyUnramified T.left.hom]
      [AlgebraicGeometry.Thickening.IsUniversalFirstOrder T],
      T.left.left.Modules)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalSheaf_eq :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.Thickening.Over X)
      [AlgebraicGeometry.FormallyUnramified T.left.hom]
      [AlgebraicGeometry.Thickening.IsUniversalFirstOrder T],
      AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalSheaf T =
        AlgebraicGeometry.Scheme.Hom.conormalSheaf T.hom.left)
