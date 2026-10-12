/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Sheaf

/-!
# Proper-hypercovering sites

Convenience import for the basic big `ph` topology, its affine restriction,
and the reusable singleton-cover sheaf criteria.  Applications that only need
the topology should import `Ph.Basic`; applications using sections and sheaf
conditions should import `Ph.Sheaf` directly.
-/
