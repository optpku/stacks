module

import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.3

The two-out-of-three principle for components of a morphism of distinguished
triangles is already owned by Mathlib's `Pretriangulated` namespace.
-/

@[stacks 014A] #check @CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃

@[stacks 014A] #check @CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂

@[stacks 014A] #check @CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃
