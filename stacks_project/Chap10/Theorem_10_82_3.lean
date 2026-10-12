/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Criteria
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.82.3
@stack 058K

Theorem 10.82.3 is recalled from the neutral criterion API.  Its tagged main
statement is `CategoryTheory.ShortComplex.UniversallyExact.Criteria.tfae`.
-/

@[stacks 058K "(1) universally exact owner"]
#check @CategoryTheory.ShortComplex.UniversallyExact

@[stacks 058K "universally exact tensor consequence"]
#check CategoryTheory.ShortComplex.UniversallyExact.tensorRight_shortExact

@[stacks 058K "isomorphism invariance"]
#check CategoryTheory.ShortComplex.UniversallyExact.of_iso

@[stacks 058K "(2) finitely presented tensor criterion"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.tensorRight

@[stacks 058K "(3) equational criterion"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.equational

@[stacks 058K "(4) finite-free square criterion"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.finiteFreeSquare

@[stacks 058K "(5) Hom-surjectivity criterion"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.homSurjective

@[stacks 058K "(6) filtered split-colimit criterion"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.filteredSplitColimit

@[stacks 058K "six-way equivalence"]
#check CategoryTheory.ShortComplex.UniversallyExact.Criteria.tfae
