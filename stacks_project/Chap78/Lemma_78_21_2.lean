module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.IsoComma
import StacksCheckRecall

universe u

/- Lemma 78.21.2. The canonical square associated to a morphism of groupoids in algebraic
spaces identifies the quotient of its iso-comma groupoid with the two-fibre product of the
induced quotient-stack morphism and the target atlas. -/
@[stacks 04Y4] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaCone_isBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B}
      (f : AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H),
      CategoryTheory.Bicategory.PseudoPullbackCone.IsBilimit
        (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaCone f))
