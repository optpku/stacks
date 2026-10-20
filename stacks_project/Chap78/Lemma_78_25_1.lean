module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Restriction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 78.25.1. The induced morphism of quotient stacks is fully faithful if
and only if the source arrow space is the restriction of the target arrow space
along the object map. -/
@[stacks 046S] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap_fullyFaithful_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H),
      Nonempty f.quotientStackMap.toFunctor.FullyFaithful ↔
        AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.IsRestriction f)
