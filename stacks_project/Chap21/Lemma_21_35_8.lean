/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.8

The unit from an object to a tensor/internal Hom is intrinsic to every braided closed monoidal
category.  The ringed-site derived category contributes no additional data, so this item recalls
the generic owner and its reusable specification and naturality API.
-/

/- Lemma 21.35.8 (0A99): the canonical morphism
`K ⟶ RHom(L, K ⊗ L)`. -/
@[stacks 0A99 "tensor/internal-Hom unit"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit

@[stacks 0A99 "tensor/internal-Hom unit specification"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec

@[stacks 0A99 "tensor/internal-Hom unit naturality in the tensor factor"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left

@[stacks 0A99 "tensor/internal-Hom unit naturality in the internal-Hom factor"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right
