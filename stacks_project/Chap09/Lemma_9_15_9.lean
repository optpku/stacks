/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.Counting
import StacksCheckRecall

@[expose] public section

/- Lemma 9.15.9 (Tag 09HS): for a finite extension `E/F`, the number of `F`-automorphisms of
`E` is at most `Field.finSepDegree F E`, with equality exactly when `E/F` is normal. -/
@[stacks 09HS]
#check FieldExtension.natCardGalLeFinSepDegree
#check FieldExtension.natCardGalEqFinSepDegreeIffNormal
