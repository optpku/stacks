/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.FiniteCoverings
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.52.4

The finite-cofinal-covering bridge is owned by the ringed-site cohomology and compactness
modules.  The source-facing entry keeps only the Stacks-labelled recall of that API.
-/

/- Lemma 21.52.4 (0G22): finite cofinal coverings force the localized degree-zero generator to be
compact relative to bounded-below derived coproducts. -/
@[stacks 0G22]
#check @RingedSite.Hom.ModuleDerived.LocalizedGenerator.isCompactOnBoundedBelow_of_finiteCoverings

#check @RingedSite.Hom.ModuleCohomology.preservesCoproducts_of_finiteCoverings
#check @CategoryTheory.IsCompactObjectOn.preservesColimit
