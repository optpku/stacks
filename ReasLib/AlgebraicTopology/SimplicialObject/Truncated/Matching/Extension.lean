/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.Construction
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.PartialRightAdjoint

/-!
# One-step extensions from matching objects

This facade exports represented matching families, the abstract extension universal property,
the explicit construction, and its partial-right-adjoint comparison. Consumers should import the
smallest semantic leaf that owns the declarations they use.
-/

@[expose] public section
