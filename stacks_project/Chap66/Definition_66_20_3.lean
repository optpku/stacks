module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionSupport
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

/- Definition 66.20.3 (1): the support of an abelian sheaf is the set of points of `|X|`
at which the geometric stalk is nonzero for any (some) geometric point over that point. -/
@[stacks 04KA] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    Sheaf (AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u + 1} →
      Set (AlgebraicSpace.Points X))

/- Definition 66.20.3 (2): the support of a section is the closed complement of the largest
open on which the section restricts to zero. -/
@[stacks 04KA] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSectionSupport :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    (F : Sheaf (AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u + 1}) →
    (U : AlgebraicSpace.smallEtaleSite X) → F.obj.obj (op U) → Closeds U.left.left)
