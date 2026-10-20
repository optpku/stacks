/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric

/-!
# Lemma 15.58.1

@stack 0FNI

The symmetric monoidal structure on integer cochain complexes is the Koszul
structure owned by ReasLib.  The historical chapter alias had no consumers,
so this entry recalls the canonical instances directly.
-/

@[expose] public section

/- Lemma 15.58.1: integer cochain complexes carry the canonical Koszul
symmetric monoidal structure. -/
@[stacks 0FNI "symmetric monoidal structure on cochain complexes"]
#check @CochainComplex.Koszul.symmetricCategory

#check @CochainComplex.Koszul.braidedCategory
#check @ComplexShape.upIntBraidingSigns
#check @ComplexShape.upIntSymmetrySymmetry
