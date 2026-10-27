/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine

/-!
# Quasi-compactness of the stack of stable curves

For genus at least two, the stack of stable curves over `specZ` admits a
surjective smooth atlas from a quasi-compact scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- For `2 ≤ g`, the stack of stable genus-`g` curves over `specZ` admits
a surjective smooth atlas from a quasi-compact scheme. -/
theorem isQuasiCompact_stableOfGenus (g : ℕ) (hg : 2 ≤ g) :
    ∃ (U : Over specZ) (p : Classifying.slice U ⟶ ofObjectProperty (stableOfGenus g specZ)),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace U.left :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
