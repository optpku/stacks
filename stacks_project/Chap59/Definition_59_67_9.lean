module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 59.67.9 (1): Let `k` be a field. A variety over `k` is an integral scheme whose
structure morphism is separated and of finite type. -/
@[stacks 03RE] #check
  (@AlgebraicGeometry.variety_iff :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.Variety X ↔
        AlgebraicGeometry.IsIntegral X.left ∧
          AlgebraicGeometry.IsSeparated X.hom ∧
            Scheme.Hom.FiniteType X.hom)

/- Definition 59.67.9 (2): A curve over `k` is a variety whose underlying scheme has dimension
one. -/
@[stacks 03RE] #check
  (@AlgebraicGeometry.curve_iff :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.Curve X ↔
        AlgebraicGeometry.Variety X ∧
          topologicalKrullDim X.left = 1)
