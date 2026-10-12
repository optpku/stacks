/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Cancellation for weakly étale morphisms

This module records cancellation of weak étaleness from a composite and its
right factor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A morphism is weakly étale when both its composite with a right factor and
the right factor are weakly étale. -/
theorem left_of_comp_right {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hfg : WeaklyEtale (f ≫ g)) (hg : WeaklyEtale g) : WeaklyEtale f := sorry

end AlgebraicGeometry.WeaklyEtale
