/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
import StacksCheckRecall

/-!
# Lemma 18.32.4

Tensor closure, dual invertibility, and invertibility of evaluation are owned for module sheaves
on an arbitrary ringed site.
-/

@[expose] public section

/- Lemma 18.32.4 (1) (040A): tensor products of invertible modules are invertible. -/
@[stacks 040A "(1)"]
#check @CategoryTheory.MonoidalCategory.isInvertibleObject.tensor

/- Lemma 18.32.4 (2) (040A): the internal-Hom dual of an invertible module is invertible. -/
@[stacks 040A "(2), dual"]
#check @SheafOfModules.RingedSite.dual.isInvertible

/- Lemma 18.32.4 (2) (040A), evaluation clause: evaluation against the internal-Hom dual is an
isomorphism. -/
@[stacks 040A "(2), evaluation"]
#check @SheafOfModules.RingedSite.dual.evaluationIsIso
