/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Additive.Biproduct
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasBinaryBiproducts D]
variable (F : C ⥤ D)

/- Lemma 12.7.1 [0DLP]: additivity is equivalent to invertibility of either
canonical binary biproduct comparison. -/
@[stacks 0DLP]
#check (F.additive_tfae_biprodComparison_isIso :
  List.TFAE [F.Additive,
    ∀ X Y : C, IsIso (F.biprodComparison' X Y),
    ∀ X Y : C, IsIso (F.biprodComparison X Y)])

#check F.additive_iff_biprodComparison'_isIso
#check F.additive_iff_biprodComparison_isIso

end CategoryTheory
