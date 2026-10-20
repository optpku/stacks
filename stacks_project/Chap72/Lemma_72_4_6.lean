/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal.GlobalSections
import StacksCheckRecall

/-!
# Global sections of a normal integral algebraic space

The ring of global sections of a normal integral algebraic space is a normal domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.4.6: Let `S` be a scheme. Let `X` be a normal integral algebraic space
over `S`. Then `Γ(X, 𝒪_X)` is a normal domain. -/
@[stacks 0BH3] #check
  (AlgebraicGeometry.AlgebraicSpace.isNormalDomain_globalSectionsRing :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNormal X] [IsIntegral X],
      IsDomain (globalSectionsRing X) ∧ IsNormalRing (globalSectionsRing X))

end AlgebraicGeometry.AlgebraicSpace
