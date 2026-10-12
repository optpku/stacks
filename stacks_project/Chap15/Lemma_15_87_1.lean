/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.AddCommGrp
import StacksCheckRecall

/-!
# Lemma 15.87.1

@stack 07KW
-/

@[expose] public section

/-
Lemma 15.87.1 (Stacks 07KW): for a sequential inverse system of abelian groups, the derived
inverse limit has cohomology only in degrees `0` and `1`; in degree zero the system is represented
by the explicit two-term Milnor complex; Mittag-Leffler systems are right acyclic; and every
complex admits a termwise right-acyclic replacement whose ordinary inverse-limit complex computes
the total right-derived functor.

The reusable owners are kept separate by mathematical role:
`DerivedLimit.RightDerived.isZero_of_one_lt`,
`DerivedLimit.Vanishes.inDegree_two`,
`DerivedLimit.Milnor.singleIso`,
`SequentialInverseSystem.IsMittagLeffler.Limit.rightAcyclic`, and
`DerivedLimit.RightAcyclic.hasMonoEmbedding`.
The termwise replacement and computation clauses are the generic
`Functor.RightAcyclic.Unbounded.Termwise` API, specialized by the degree-two vanishing bound.
-/

@[stacks 07KW "(1), higher derived limits vanish"]
#check @CategoryTheory.DerivedLimit.RightDerived.isZero_of_one_lt

#check @CategoryTheory.DerivedLimit.Vanishes.inDegree_two

@[stacks 07KW "(2), the Milnor complex computes the derived limit"]
#check @CategoryTheory.DerivedLimit.Milnor.singleIso

@[stacks 07KW "(3), Mittag-Leffler towers are right acyclic"]
#check @CategoryTheory.SequentialInverseSystem.IsMittagLeffler.Limit.rightAcyclic

#check @CategoryTheory.SequentialInverseSystem.IsMittagLeffler.r1_isZero

#check @CategoryTheory.DerivedLimit.RightAcyclic.hasMonoEmbedding

#check @CategoryTheory.Functor.RightAcyclic.Unbounded.everywhereDefined_of_vanishes

@[stacks 07KW "(4), termwise right-acyclic replacement"]
#check @CategoryTheory.Functor.RightAcyclic.Unbounded.Termwise.existsQuasiIsoTo

@[stacks 07KW "(5), termwise inverse limits compute the derived limit"]
#check @CategoryTheory.Functor.RightAcyclic.Unbounded.Termwise.computesAt
