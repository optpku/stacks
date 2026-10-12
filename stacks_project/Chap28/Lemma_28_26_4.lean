/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 28.26.4: if `U` is affine and `s` is a global section of an invertible
`𝒪_X`-module `L`, then `U ⊓ X_s` is affine. -/
@[stacks 01PV] #check
  (AlgebraicGeometry.IsAffineOpen.inf_sectionNonvanishingOpen :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
      (hU : AlgebraicGeometry.IsAffineOpen U) (L : X.Modules)
      [hL : AlgebraicGeometry.Scheme.Modules.Invertible L] (s : Γ(L, ⊤)),
      AlgebraicGeometry.IsAffineOpen (U ⊓ hL.sectionNonvanishingOpen s))
