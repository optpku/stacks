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
# Iterated derived internal Hom

Lemma 15.74.1 (0A65): the iterated derived internal-Hom currying isomorphism, relative to an
explicit fixed-right derived tensor model, is owned by `InternalHom.TensorSource`.

@stack 0A65
-/

/- Lemma 15.74.1 (0A65): canonical currying and its naturality in all three variables. -/
@[stacks 0A65 "iterated derived internal-Hom currying"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorSource.isoOf

#check @CategoryTheory.DerivedCategory.InternalHom.TensorSource.isoOf_natural_left
#check @CategoryTheory.DerivedCategory.InternalHom.TensorSource.isoOf_natural_middle
#check @CategoryTheory.DerivedCategory.InternalHom.TensorSource.isoOf_natural_right

#print axioms CategoryTheory.DerivedCategory.InternalHom.TensorSource.isoOf
