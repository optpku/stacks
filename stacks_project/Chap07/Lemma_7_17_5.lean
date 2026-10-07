module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf.Representable
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.5

Locally-surjective descent of quasi-compactness is owned by ReasLib; this
file is the labelled source-facing recall layer.
-/

@[expose] public section

/- Lemma 7.17.5 (0GMP) (1): a locally-surjective sheafified-representable
map transports quasi-compactness to its target site object. -/
@[stacks 0GMP "(1)"] #check @CategoryTheory.GrothendieckTopology.QuasiCompactObject.of_sheafifiedRepresentableMap

/- Lemma 7.17.5 (0GMP) (2): a locally-surjective image of a quasi-compact
sheaf of sets is quasi-compact. -/
@[stacks 0GMP "(2)"] #check @CategoryTheory.Sheaf.IsQuasiCompactObject.of_locallySurjective

#check @CategoryTheory.Sheaf.IsQuasiCompactObject.isClosedUnderQuotients
