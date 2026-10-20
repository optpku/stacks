module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Associativity
import StacksCheckRecall

/-!
# Derived monoidal structure

The derived monoidal and symmetric structures are supplied by the K-flat localization owner.
Their tensor-descends and localization hypotheses remain visible in the owner signatures; this
file does not install an unconditional derived monoidal structure or choose a tensor model.

@stack 0FNQ
-/

@[expose] public section

/- The monoidal structure produced by K-flat localization. -/
#check @CategoryTheory.DerivedCategory.KFlat.monoidalCategory

/- Lemma 15.127.1: K-flat localization supplies the symmetric derived monoidal structure. -/
@[stacks 0FNQ "K-flat symmetric derived monoidal structure"]
#check @CategoryTheory.DerivedCategory.KFlat.symmetricCategory

/- Source-facing associativity and symmetry use the explicit-model and canonical bifunctor
owners, respectively. -/
#check @CategoryTheory.DerivedCategory.DerivedTensor.Right.assoc
#check @CategoryTheory.DerivedCategory.DerivedTensorProduct.comm
