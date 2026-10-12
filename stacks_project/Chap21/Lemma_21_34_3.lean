/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.3

The tensor/internal-Hom comparison and all three variance directions are owned by the generic
braided closed monoidal API.  A ringed-site complex category is only a specialization of that
owner, so this chapter item does not introduce a second comparison map or ringed-site-specific
naturality proofs.
-/

/- Lemma 21.34.3 (0BYT): for a braided closed monoidal category, the canonical source-order map
`K ⊗ (ihom M).obj L ⟶ (ihom M).obj (K ⊗ L)`. -/
@[stacks 0BYT "source-order tensor/internal-Hom comparison"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison

/- Lemma 21.34.3 (0BYT): the uncurried evaluation specification. -/
@[stacks 0BYT "tensor/internal-Hom evaluation specification"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_uncurry

/- Lemma 21.34.3 (0BYT): naturality in the tensor factor. -/
@[stacks 0BYT "tensor/internal-Hom tensor naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_tensor

/- Lemma 21.34.3 (0BYT): naturality in the internal-Hom target. -/
@[stacks 0BYT "tensor/internal-Hom target naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_target

/- Lemma 21.34.3 (0BYT): contravariant naturality in the internal-Hom source. -/
@[stacks 0BYT "tensor/internal-Hom source naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_source
