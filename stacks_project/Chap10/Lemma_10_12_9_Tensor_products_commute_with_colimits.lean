/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.12.9 (Tensor products commute with colimits) (Tag 00DD).

@stack 00DD
-/

open CategoryTheory Limits MonoidalCategory

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I]
variable (N : ModuleCat.{u} R) (F : I ⥤ ModuleCat.{u} R) [HasColimit F]

-- Lemma 10.12.9: the colimit of `Mᵢ ⊗ N` is canonically isomorphic to
-- `(colimit Mᵢ) ⊗ N`. The source orientation is the inverse of Mathlib's
-- canonical preservation isomorphism.
@[stacks 00DD]
#check (preservesColimitIso (tensorRight N) F).symm

-- The inverse preservation isomorphism has the expected formula on each cocone leg.
@[stacks 00DD "colimit comparison leg"]
#check @CategoryTheory.ι_preservesColimitIso_inv

end
