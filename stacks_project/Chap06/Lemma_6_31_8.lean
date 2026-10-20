/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OpenSubsetExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubsetExtensionByInitial
import StacksCheckRecall

@[expose] public section

/- Lemma 6.31.8 (1): module-presheaf extension by zero is left adjoint to restriction to the
open subspace. -/
@[stacks 00A7 "presheaf module extension-restriction adjunction"]
recall PresheafOfModules.OpenSubset.ExtensionByZero.adjunction

/- Lemma 6.31.8 (2): module-sheaf extension by zero is left adjoint to restriction to the open
subspace. -/
@[stacks 00A7 "sheaf module extension-restriction adjunction"]
recall SheafOfModules.OpenSubset.ExtensionByZero.adjunction

/- Lemma 6.31.8 (3), outside the open subset: the stalk module of extension by zero is zero. -/
@[stacks 00A7 "stalk of module extension outside the open subspace"]
recall SheafOfModules.OpenSubset.ExtensionByZero.stalk_isZero_of_not_mem

/- Lemma 6.31.8 (3), inside the open subset: the canonical unit induces an isomorphism on stalk
modules. -/
@[stacks 00A7 "stalk of module extension inside the open subspace"]
recall SheafOfModules.OpenSubset.ExtensionByZero.unit_stalk_isIso

/- Lemma 6.31.8 (4): restriction after module extension by zero is naturally isomorphic to the
identity. -/
@[stacks 00A7 "restriction after module extension by zero"]
recall SheafOfModules.OpenSubset.ExtensionByZero.unit_isIso
