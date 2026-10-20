/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral.GlobalSections
import StacksCheckRecall

/-!
# Global sections of an integral algebraic space

The ring of global sections of an integral algebraic space is a domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 72.4.4: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. Then `Γ(X, 𝒪_X)` is a domain. -/
@[stacks 0BH2] #check (AlgebraicGeometry.AlgebraicSpace.instIsDomain_globalSectionsRing : ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} [AlgebraicGeometry.AlgebraicSpace.IsIntegral X], IsDomain (AlgebraicGeometry.AlgebraicSpace.globalSectionsRing X))
