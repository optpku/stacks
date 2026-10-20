module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Fiber
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Precomposition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Postcomposition

/-!
# Equivalences of based categories over a base

Compatibility aggregate for the equivalence-over-base API: explicit heterogeneous
`BasedFunctor.QuasiInverse` data, property and bicategorical interfaces, total-category and
fiberwise consequences, and equivalences induced on based-functor hom-categories by
precomposition or postcomposition.

New consumers that need only one consequence should import its leaf module directly.
-/
