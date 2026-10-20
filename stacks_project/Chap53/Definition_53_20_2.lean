module

public import stacks_project.Chap53.Lemma_53_20_1
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Definition 53.20.2: a morphism of schemes `f : X ⟶ S` is at-worst-nodal of
relative dimension `1` when it satisfies the equivalent conditions of Lemma 53.20.1. -/
@[stacks 0C5A] #check
  (AlgebraicGeometry.AtWorstNodal :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → Prop)

#check AlgebraicGeometry.atWorstNodal_iff
#check AlgebraicGeometry.fibersAtWorstNodal_iff_syntomicAndSingularUnramified
