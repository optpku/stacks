module

public import stacks_project.Chap39.Definition_39_3_1_PreRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 39.13.3: an equivalence relation over a scheme has a unique composition on
composable arrows, characterized by its target and source. -/
@[stacks 0233] #check
  (AlgebraicGeometry.Scheme.PreRelation.existsUniqueComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}
        (P : AlgebraicGeometry.Scheme.PreRelation U) [IsEquivalenceRelation P.t P.s],
      ∃! c : pullback P.s P.t ⟶ P.left,
        c ≫ P.t = pullback.fst P.s P.t ≫ P.t ∧
          c ≫ P.s = pullback.snd P.s P.t ≫ P.s)
