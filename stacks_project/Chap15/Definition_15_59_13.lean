/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.59.13

@stack 064M

The representative, canonical fixed-right derived functor, exactness instances, and notation live
in ReasLib.  This chapter file is only the tagged source recall.
-/

/- Definition 15.59.13, tag `064M`: the unbounded derived tensor functor
`- ⊗[R]^L M : D(R) ⥤ D(R)`. -/
@[stacks 064M "derived tensor functor"]
#check CategoryTheory.DerivedCategory.derivedTensorProduct

/- The reusable shift-compatibility instance. -/
#check @CategoryTheory.derivedTensorProduct_commShift

/- The reusable triangulated exactness theorem. -/
#check @CategoryTheory.derivedTensorProduct_isTriangulated
