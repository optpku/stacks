/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.InternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.8

The K-injective internal-Hom criterion is owned at the coefficient-category-generic level for the
canonical cochain internal-Hom construction.  A ringed-site module complex is a specialization of
this API, so the chapter item is a direct reusable recall rather than a second ringed-site theorem
with proof-local instances.
-/

/- Lemma 21.34.8 (0A96): if `L` is K-flat and `I` is K-injective, the internal-Hom complex from
`L` to `I` is K-injective. -/
@[stacks 0A96 "K-injective internal-Hom criterion"] #check
  @CategoryTheory.CochainComplex.InternalHom.isKInjective_of_isKFlat
