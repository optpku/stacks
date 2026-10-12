/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_20_3_EtaleSupport
import StacksCheckRecall

/- Definition 66.20.3 (1): the support of an abelian sheaf is the set of points of `|X|`
at which the geometric stalk is nonzero for any (some) geometric point over that point. -/
@[stacks 04KA] #check AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport

/- Definition 66.20.3 (2): the support of a section is the closed complement of the largest
open on which the section restricts to zero. -/
@[stacks 04KA] #check AlgebraicGeometry.AlgebraicSpace.abelianSheafSectionSupport
