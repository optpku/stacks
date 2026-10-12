/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.StandardAffine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Big

/-!
# Syntomic site infrastructure

Convenience import for the canonical syntomic affine restriction, the separate
finite-standard-chart presentation, and the big-slice sheaf functor API.
Applications needing only one layer should import its narrower leaf directly.
-/
