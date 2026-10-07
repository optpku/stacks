module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Colimit

/-!
# Lemma 81.3.1

A scheme-colimit of schemes over `S` remains a colimit in algebraic spaces over `S`
under surjectivity of `∐ X_i ⟶ X`, étale base-change of the colimit, and an essential-image
hypothesis on separated cartesian étale systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

/- Lemma 81.3.1: A scheme colimit satisfying the étale base-change and descent criteria is also
a colimit in algebraic spaces after applying `schemeFunctor`. -/
@[stacks 07SX] #check (AlgebraicGeometry.AlgebraicSpace.isColimit_ofOver :
  ∀ {J : Type v} [Category.{v} J] [Small.{u} J] {S : Scheme.{u}},
    (D : J ⥤ Over S) → (c : Cocone D) →
    IsColimit ((Over.forget S).mapCocone c) →
    AlgebraicGeometry.Surjective (AlgebraicGeometry.Scheme.coproductToColimit c) →
    (∀ {U : Scheme.{u}} (f : U ⟶ c.pt.left) [AlgebraicGeometry.Etale f],
      IsColimit (AlgebraicGeometry.Scheme.etalePullbackCocone c f)) →
    (∀ U : AlgebraicGeometry.Scheme.CartesianEtaleSystem D,
      (∀ i, AlgebraicGeometry.IsSeparated (U.π.app i)) →
        AlgebraicGeometry.Scheme.IsInEtaleEssImage c U) →
    Nonempty (IsColimit ((AlgebraicGeometry.AlgebraicSpace.schemeFunctor S).mapCocone c)))
