/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.2

Derived-limit preservation and the objectwise Milnor row are owned by the reusable
`ModuleSections` API.  The cohomology tower is `ModuleSections.Underlying.cohomologyTower`; no
chapter compatibility alias is needed.
-/

/- Lemma 21.23.2 (1) (0D6K): module-valued derived sections over an object preserve sequential
derived limits. -/
@[stacks 0D6K "(1)"]
#check @RingedSite.Hom.ModuleSections.sectionsDerived_preservesDerivedLimit

/- Lemma 21.23.2 (2) (0D6K): underlying additive derived sections preserve sequential derived
limits. -/
@[stacks 0D6K "(2)"]
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsDerived_preservesDerivedLimit

/- Lemma 21.23.2 (3) (0D6K): objectwise cohomology of a sequential derived limit lies in the
canonical Milnor short exact sequence. -/
@[stacks 0D6K "(3)"]
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyShortExact

#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyTower
#check @CategoryTheory.SequentialInverseSystem.firstDerivedLimit
#check @CategoryTheory.IsDerivedLimit.cohomologyShortExact
