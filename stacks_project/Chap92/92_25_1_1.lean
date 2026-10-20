/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.«92_25_1_1_Morphism»
public import stacks_project.Chap92.«92_25_1_1_Site»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.CotangentSite

/- 92.25.1.1 (1): the morphism of ringed topoi
i : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(C_{X/Λ}), O)
is the identity on underlying topoi, with i♯ : O ⟶ underline{O}_X the obvious map. -/
@[stacks 08VA]
#check AlgebraicGeometry.Scheme.CotangentSite.i

/- 92.25.1.1 (2): the morphism of ringed topoi
π : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(X_Zar), O_X)
is induced by the forgetful functor u : C_{X/Λ} ⥤ X_Zar. -/
@[stacks 08VA]
#check AlgebraicGeometry.Scheme.CotangentSite.toZariski
