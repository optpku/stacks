/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology

/-!
# Lemma 15.60.3

@stack 0GMT

Derived extension of scalars is left adjoint to derived restriction of scalars.  ReasLib owns
the adjunction and homology comparison for an explicit ring homomorphism.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.60.3 (0GMT): derived extension of scalars is left adjoint to derived restriction of
scalars. -/
@[stacks 0GMT "derived extension-restriction adjunction"]
#check @ModuleCat.derivedExtensionRestrictionAdjunction

#check @ModuleCat.derivedExtensionRestrictionHomEquiv
#check @ModuleCat.derivedRestrictionHomologyIso
#check @ModuleCat.derivedExtensionHomologyComparison

#print axioms ModuleCat.derivedExtensionRestrictionAdjunction
