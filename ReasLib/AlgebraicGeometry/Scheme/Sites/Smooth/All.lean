/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.StandardAffine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Big

/-!
# Smooth site infrastructure

Convenience import for the canonical smooth affine restriction, the separate
finite-standard-chart presentation, and the big-slice sheaf functor API.
Applications needing only one layer should import its narrower leaf directly.
-/
