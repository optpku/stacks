/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.4

The tensor/internal-Hom unit and its coherence laws are generic braided closed-monoidal data.  The
ringed-site complex category is only a specialization of these owners.
-/

/- Lemma 21.34.4 (0A93): tensor/internal-Hom unit. -/
@[stacks 0A93 "tensor/internal-Hom unit"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit

@[stacks 0A93 "tensor/internal-Hom unit specification"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec
@[stacks 0A93 "tensor/internal-Hom unit left naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left
@[stacks 0A93 "tensor/internal-Hom unit right naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right
