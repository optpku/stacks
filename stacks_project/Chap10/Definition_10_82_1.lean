/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.82.1

@stack 058I
-/

/- Definition 10.82.1 (1): tensor-stable injectivity is the shared
`LinearMap.UniversallyInjective` predicate. -/
@[stacks 058I "universally injective map"]
#check LinearMap.UniversallyInjective
@[stacks 058I "tensor injectivity"]
#check LinearMap.UniversallyInjective.rTensor_injective

/- Definition 10.82.1 (2): universal exactness of a module short complex is the shared
`CategoryTheory.ShortComplex.UniversallyExact` predicate. -/
@[stacks 058I "universally exact short complex"]
#check CategoryTheory.ShortComplex.UniversallyExact
@[stacks 058I "underlying short exactness"]
#check CategoryTheory.ShortComplex.UniversallyExact.shortExact
@[stacks 058I "universally injective first map"]
#check CategoryTheory.ShortComplex.UniversallyExact.universallyInjective_f
