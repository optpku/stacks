module

public import StacksCheckRecall.CommandCrossRef
public import stacks_project.Chap85.Lemma_85_15_3_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization

/- Lemma 85.15.3 (1): for `K` in `SR(C)`, the functor `j_!` is the comparison
`comparison J K` into the slice over `sheafified J K`, and this comparison is an
equivalence `Sheaf (overTopology J K) (Type (max w v)) ⥤ Over (sheafified J K)`. -/
@[stacks 0D87] #check @comparison.isEquivalence

/- Lemma 85.15.3 (2): via the identification of (1), inverse image along `j` corresponds to
`Over.star` at `sheafified J K`, i.e. `F ↦ (F ⨯ F(K)^# ⟶ F(K)^#)`. -/
@[stacks 0D87] #check @inverseImageComparison_isIso

/- Lemma 85.15.3 (3): for `φ : K ⟶ L` in `SR(C)`, inverse image along relocalization
corresponds via the identifications of (1) to `Over.pullback` along
`sheafifiedMap J φ : sheafified J K ⟶ sheafified J L`. -/
@[stacks 0D87] #check @relocalizationInverseImageComparison_isIso
