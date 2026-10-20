/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SectionLocalization
import StacksCheckRecall

/-!
# Lemma 18.44.2

Localization of module sheaves is the same-site pullback along the localized coefficient sheaf.
The adjunction supplies its universal property, and the change-of-rings comparison identifies it
with extension of scalars.
-/

@[expose] public section

/- Lemma 18.44.2 (0EMD): the canonical localization functor on module sheaves. -/
#check @SheafOfModules.RingedSite.SectionLocalization.functor

/- Lemma 18.44.2 (0EMD): localization is left adjoint to restriction along the localized
coefficient sheaf. -/
#check @SheafOfModules.RingedSite.SectionLocalization.adjunction

/- Lemma 18.44.2 (0EMD) (1): the resulting universal factorization property. -/
@[stacks 0EMD "(1), universal property"]
#check @SheafOfModules.RingedSite.SectionLocalization.existsUnique_lift

/- Lemma 18.44.2 (0EMD) (2): the localized module is extension of scalars, i.e. the categorical
form of the localized coefficient sheaf tensored with the original module. -/
@[stacks 0EMD "(2), extension of scalars"]
#check @SheafOfModules.RingedSite.SectionLocalization.extensionIso
