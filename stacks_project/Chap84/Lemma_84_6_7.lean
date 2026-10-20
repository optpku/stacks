module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Descent
import StacksCheckRecall

/-!
# Lemma 84.6.7

In the setup of Lemma 84.6.4, if `f : X ⟶ Y` is flat, locally of finite
presentation, and surjective, then the functor from sheaves on `Y_étale` to
the iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`, is an equivalence. Printed sheaves on
`(Sch/Y)_fppf` are the Lemma 84.3.1 view of sheaves on `(Spaces/Y)_fppf`.
The scheme comparison is used after étale localization of the target to a scheme.
-/

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 84.6.7: the canonical comparison functor for a flat, locally finitely
presented, surjective morphism of algebraic spaces is an equivalence. -/
@[stacks 0DGL] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.fppfSmallIsoCommaFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicSpace.Surjective f],
      (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.fppfSmallIsoCommaFunctor f).IsEquivalence)
