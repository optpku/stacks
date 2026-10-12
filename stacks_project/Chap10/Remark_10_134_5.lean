/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Transitivity
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.134.5

@stack 07VC

The chapter item is a canonical self-presentation specialization of the
shared target-changing naive-cotangent API.  The general presentation map and
parallel-map homotopy belong to ReasLib, rather than to this source recall.
-/

/- Remark 10.134.5 [stacks 07VC]: for a tower of commutative rings
`A → B → C`, the canonical comparison
`NL{B⁄A} ⟶ NL{C⁄B}↾[B]` is chain-homotopic to zero.  Its degree-lowering
map is the difference between the generator and coefficient presentation
morphisms, which formalizes the source's subtraction formula. -/
@[stacks 07VC]
#check @Algebra.NaiveCotangent.Transitivity.nullHomotopy

#check @Algebra.NaiveCotangent.Transitivity.comparison
#check @Algebra.NaiveCotangent.Transitivity.constant
#check @Algebra.Extension.NaiveCotangent.RestrictScalars.map
#check @Algebra.Extension.NaiveCotangent.RestrictScalars.mapHomotopy
