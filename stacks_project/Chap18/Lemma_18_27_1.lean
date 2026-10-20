/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SectionAction
import StacksCheckRecall

/-!
# Lemma 18.27.1

Compatibility facade for internal Hom from a module presheaf.  ReasLib owns
the sheafification-based construction and its comparison with the canonical
closed-monoidal owner `ihom`.
-/

@[expose] public section

open CategoryTheory

/- Lemma 18.27.1 (03EM): a module presheaf source is sheafified before applying the
canonical internal-Hom functor. -/
@[stacks 03EM "presheaf source"]
#check @SheafOfModules.RingedSite.InternalHom.fromPresheaf

/- For a source which already is a module sheaf, this construction canonically agrees with
`ihom`. -/
@[stacks 03EM "sheaf source"]
#check @SheafOfModules.RingedSite.InternalHom.fromPresheafValIso

/- The objectwise scalar-action infrastructure used by the traditional slice-Hom description
is independently reusable. -/
#check @PresheafOfModules.SectionAction.action
