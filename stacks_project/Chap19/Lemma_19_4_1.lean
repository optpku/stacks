/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian
import StacksCheckRecall

@[expose] public section

/-!
# Injectives in Abelian Sheaves on a Space

The reusable instance chain is owned for abelian sheaves on an arbitrary site.  This file only
records its specialization to the source notation `Ab(X)`.
-/

open CategoryTheory
open scoped TopCat

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u})

/- Lemma 19.4.1 (1): the category `Ab(X)` of abelian sheaves on a topological space has enough
injectives. -/
@[stacks 01DG "enough injectives"] #check
  (inferInstance : EnoughInjectives (Ab(X)))

/- Lemma 19.4.1 (2): injective embeddings in `Ab(X)` can be chosen functorially. -/
@[stacks 01DG "functorial injective embeddings"] #check
  (inferInstance : HasFunctorialInjectives (Ab(X)))

end TopCat
