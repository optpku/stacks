/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Diagram
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Presheaf
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Cone
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Degeneracy
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Limit
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Map
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.SimplicialSet

/-!
# Matching families for truncated simplicial objects

This import aggregate exports explicit compatible face families, their equivalence with matching
cones, the canonical matching object, face and degeneracy coordinates, and the one-step extension
API. Import a leaf module when only one layer is needed.
-/

@[expose] public section
