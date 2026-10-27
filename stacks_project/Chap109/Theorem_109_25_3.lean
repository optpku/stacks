/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable.SmoothLocus

/-!
# Properties of the moduli stack of stable curves of genus `g`

For `g ≥ 2`, the algebraic stack `ℳ̄_g` is Deligne–Mumford, proper and smooth
over `Spec ℤ`, and the locus `ℳ_g` of smooth curves is a dense open substack.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Theorem 109.25.3: for `g ≥ 2`, the stack of stable genus-`g` curves is
Deligne–Mumford, proper and smooth over `Spec ℤ`, with dense open smooth locus. -/
@[stacks 0E9C] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instProper_stableOfGenus :
    ∀ (g : ℕ) [Nat.AtLeastTwo g],
      CohStack.Hom.Proper
        (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instDeligneMumfordStack_stableOfGenus :
    ∀ (g : ℕ) [Nat.AtLeastTwo g] (S : Scheme.{u}),
      CohStack.DeligneMumfordStack (ofObjectProperty (stableOfGenus g S)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_toIdentitySlice_stableOfGenus :
    ∀ (g : ℕ) [Nat.AtLeastTwo g] (S : Scheme.{u}),
      CohStack.Hom.Smooth
        (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g S))))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instOpenImmersion_inclusionSmoothStableOfGenus :
    ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}),
      CohStack.OpenImmersion (inclusionSmoothStableOfGenus g hg S))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dense_smoothH0OfGenusPointsSet :
    ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}),
      Dense (Set.range (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S))))
