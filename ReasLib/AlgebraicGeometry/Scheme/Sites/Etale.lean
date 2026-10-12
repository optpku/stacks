/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

/-!
# Etale site infrastructure

Convenience import for the source-scheme functor of the small etale site and
the affine restrictions of the big and small etale sites, together with their
cross-layer topos relation API. Applications using only one layer should
import its narrower leaf directly.
-/
