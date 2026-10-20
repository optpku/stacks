/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf

/-!
# Glued descent construction recall

The construction-specific comparison has been replaced by the canonical
family pullback comparison and the effective descent theorem for localized
`Type`-valued sheaves.
-/

@[expose] public section

#check @CategoryTheory.DescentDatum.Pullback.canonicalIso
#check @CategoryTheory.DescentDatum.Pullback.iso
#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_isEquivalence
