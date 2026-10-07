module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.9.4: the structure morphism of an abelian variety over a field is smooth. -/
@[stacks 0BFC] #check
  (AlgebraicGeometry.AbelianVariety.instSmooth :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A],
      Smooth A.hom)
