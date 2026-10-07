module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Projective

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.9.2: the structure morphism of an abelian variety over a field is projective. -/
@[stacks 0BFA] #check
  (AlgebraicGeometry.AbelianVariety.instProjective :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A],
      Projective A.hom)
