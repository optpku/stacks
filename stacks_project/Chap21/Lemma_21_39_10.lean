/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.Chaotic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.39.10

The source statement is the diagonal specialization of the reusable pointlike lower-shriek/tensor
owner.  The shared theorem keeps the pointlike witness and uses the canonical two-variable derived
tensor on both the module-presheaf and module categories; this file is only the source-facing
recall surface.  The second recall identifies this presheaf model with modules over the constant
ring sheaf on the chaotic site, which is the source's `D(underline B)`.
-/

open CategoryTheory

/- Lemma 21.39.10 (08QC): if a pointlike cosimplicial object exists, `Lπ!` commutes with derived
tensor of module-valued presheaves. -/
@[stacks 08QC "pointlike derived lower-shriek tensor comparison"]
#check @CategoryTheory.DerivedColimit.Tensor.tensor_isomorphic_of_exists_pointlike

#check @ModuleCat.Presheaf.Chaotic.Constant.derived_isEquivalence
