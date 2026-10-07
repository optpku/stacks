module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.SmallSources
import StacksCheckRecall

@[expose] public section

/- Lemma 21.43.8 (0GYZ): one cardinal simultaneously bounds nonzero sources for all nonzero
objects of the canonical `ModulesOnCategory.Chaotic.QC` subcategory and the componentwise
factorizations of maps from bounded objects into countable coproducts. -/
@[stacks 0GYZ]
#check @CategoryTheory.ModulesOnCategory.Chaotic.exists_cardinal_for_small_sources

/- The reusable API separates the size function, bounded object set, two source clauses, and
the bridge to the abstract Brown-representability criterion. -/
#check @SheafOfModules.CochainComplex.derivedObjectCardinal
#check @CategoryTheory.ModulesOnCategory.Chaotic.objectCardinal
#check @CategoryTheory.ModulesOnCategory.Chaotic.boundedObjects
#check @CategoryTheory.ModulesOnCategory.Chaotic.BoundedObjectsDetectNonzero
#check @CategoryTheory.ModulesOnCategory.Chaotic.BoundedObjectsFactorCountableCoproducts
#check @CategoryTheory.ModulesOnCategory.Chaotic.boundedObjects_isSet
#check @CategoryTheory.ModulesOnCategory.Chaotic.exists_brownSet
#check @CategoryTheory.ModulesOnCategory.Chaotic.exists_smallBrownSet
