/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Legacy compatibility path for Lemma 21.45.5

The tagged source entry is `stacks_project.Chap21.Lemma_21_45_5`. This unimported historical path
only checks the same shared tensor-product API and introduces no duplicate declarations.
-/

#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.tensor
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent.tensor

end
