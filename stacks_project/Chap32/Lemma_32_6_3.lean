/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Lemma 32.6.3: for a morphism `f : X ⟶ S`, surjectivity of the functor-of-points
comparison for every directed inverse limit with affine stages implies that `f` is
locally of finite presentation. -/
@[stacks 0CM0] #check
  (AlgebraicGeometry.Scheme.Over.Yoneda.locallyFinitePresentation_of_surjective_on_affine_stages :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      (∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, AlgebraicGeometry.IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc _ ((yoneda.obj (Over.mk f)).mapCocone c.op))) →
      AlgebraicGeometry.LocallyOfFinitePresentation f)
