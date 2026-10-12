/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Monic.Transport
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Types
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Functors

/-!
# Splittings of truncated simplicial objects

This compatibility facade re-exports the construction, transport, monicity, bundled category,
type-valued morphism properties, and standard functors for split truncated simplicial objects.
Downstream modules should import the narrow semantic leaf that owns the declarations they use.
-/

@[expose] public section
