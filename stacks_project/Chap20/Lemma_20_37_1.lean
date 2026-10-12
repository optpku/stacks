/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Sections.Limit

/-
Lemma 20.37.1: for a ringed space `X`, an open subset `U ⊆ X`, and a sequential inverse
system `(K_n)` in `D(𝒪_X)` with derived limit `K`, derived sections over `U` preserve the
sequential derived limit.  In every degree `m`, the resulting open hypercohomology fits into
the Milnor short exact sequence
`0 ⟶ R¹ lim H^(m - 1)(U, K_n) ⟶ H^m(U, K) ⟶ lim H^m(U, K_n) ⟶ 0`.

The reusable owner exposes the ordinary and underlying section functors, their canonical
countable-limit instances, the derived-limit transport, and the exact homology identification.
The chapter is a recall surface only; no local derived-category instances or private tower
transport definitions are needed here.
-/

@[stacks 0D60 "Lemma 20.37.1 (1): derived sections over an open preserve sequential derived limits"]
#check @preservesDerivedLimit

@[stacks 0D60 "Lemma 20.37.1 (1), underlying additive form: derived sections preserve sequential derived limits"]
#check @underlyingPreservesDerivedLimit

@[stacks 0D60 "Lemma 20.37.1 (2): the Milnor short exact sequence for open hypercohomology"]
#check @cohomologyShortExact

@[stacks 0D60 "derived sections functor"]
#check @sectionsFunctor
@[stacks 0D60 "derived sections preserve discrete natural-number limits"]
#check @sectionsFunctor_preservesDiscreteNatLimits
@[stacks 0D60 "underlying derived sections functor"]
#check @underlyingFunctor
@[stacks 0D60 "underlying derived sections preserve discrete natural-number limits"]
#check @underlyingFunctor_preservesDiscreteNatLimits
@[stacks 0D60 "derived sections hypercohomology comparison"]
#check @hypercohomologyIso

end
