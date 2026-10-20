/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality

@[expose] public section

/-!
# Unit of the derived tensor/internal-Hom adjunction

Lemma 15.74.6 (0A6B): the unit of the derived tensor/internal-Hom adjunction, relative to an
explicit fixed-right derived tensor model, is owned by `InternalHom.unitOf`.

@stack 0A6B
-/

/- Lemma 15.74.6 (0A6B): the canonical unit and its naturality in both variables. -/
@[stacks 0A6B "derived tensor/internal-Hom adjunction unit"]
#check @CategoryTheory.DerivedCategory.InternalHom.unitOf

#check @CategoryTheory.DerivedCategory.InternalHom.unitOf_natural_left
#check @CategoryTheory.DerivedCategory.InternalHom.unitOf_natural_right
#check @CategoryTheory.DerivedCategory.InternalHom.counitOf

#print axioms CategoryTheory.DerivedCategory.InternalHom.unitOf
