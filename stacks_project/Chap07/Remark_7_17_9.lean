module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.17.9

Finite sheafified-representable coproduct test sets and the three standard
finite-basis hypotheses are reusable quasi-compactness API owned by ReasLib.
-/

@[expose] public section

/- Remark 7.17.9 (0GMS): a surjective basis, a refining basis, or
quasi-compact generators with quasi-compact representable products gives a
quasi-compact test set for filtered global sections. -/
@[stacks 0GMS "finite coproducts"] #check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.finiteRepresentableCoproducts

@[stacks 0GMS "surjective basis"] #check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.SurjectiveBasis

@[stacks 0GMS "refining basis"] #check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.RefiningBasis

@[stacks 0GMS "generators"] #check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.GeneratorHypotheses

@[stacks 0GMS "test set"] #check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.exists_of_cases
