module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Classifying
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.SheafComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.PrincipalEquivalence

/-!
# Lemma 95.15.4

The classifying stacks `[B/G]`, `[[B/G]]`, `G`-Torsors, and `𝒢/ℬ`-Torsors
are canonically equivalent over `(Sch/S)_fppf`. If `G ⟶ B` is flat and
locally of finite presentation, they are also equivalent to `G`-Principal.
-/

@[expose] public section

universe u

/- Lemma 95.15.4. The torsor-with-map quotient `[[B/G]]` for the trivial action
on the base is canonically equivalent to `G`-Torsors over `(Sch/S)_fppf`. -/
@[stacks 0CQJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toTorsors_trivialAction_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B),
      (AlgebraicGeometry.QuotientStack.GroupAction.toTorsors G
        (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction G)).toBasedFunctor.IsEquivalence)

/- The general quotient comparison, applied to `trivialAction G`, identifies
`[B/G]` with `[[B/G]]` over `(Sch/S)_fppf`. -/
#check
  (AlgebraicGeometry.QuotientStack.GroupAction.equivalent_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B)
      (X : AlgebraicGeometry.GroupAlgebraicSpace.Action G),
      (AlgebraicGeometry.QuotientStack.GroupAction.equivalent G X).toBasedFunctor.IsEquivalence)

/- The relative-points comparison identifies `G`-Torsors with `𝒢/ℬ`-Torsors. -/
#check
  (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toSheafHom_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B),
      CategoryTheory.StackOver.Groupoids.Hom.IsEquivalence
        (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toSheafHom G))

/- If `G ⟶ B` is flat and locally of finite presentation, the canonical
comparison identifies `G`-Torsors with `G`-Principal. -/
#check
  (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toPrincipal_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B)
      [AlgebraicGeometry.AlgebraicSpace.Flat G.X.hom]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation G.X.hom],
      CategoryTheory.StackOver.Groupoids.Hom.IsEquivalence
        (AlgebraicGeometry.GroupAlgebraicSpace.toPrincipal G))
