module

public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Tensor/internal-Hom comparison compatibility facade

The generic closed-monoidal owner contains the comparison map, its evaluation specification, and
all naturality laws. This former chapter owner is retained only as a recall surface for aggregate
imports; it does not define a second ringed-site-specific map.
-/

/- Lemma 21.34.3 (0BYT): canonical source-order tensor/internal-Hom comparison. -/
@[stacks 0BYT "source-order tensor/internal-Hom comparison"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison

/- Lemma 21.34.3 (0BYT): evaluation specification for the comparison. -/
@[stacks 0BYT "tensor/internal-Hom evaluation specification"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_uncurry

/- The reusable owner also records simultaneous naturality in all three inputs. -/
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural
