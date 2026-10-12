/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor

/-!
# Sections on open subsets of ringed spaces

Convenience import for ordinary, tensor, and derived section APIs on open subsets. Import
`Module.Sections.Basic`, `Module.Sections.Pushforward`, `Module.Sections.Tensor`, or
`Module.Derived.Sections` directly when a narrower dependency is appropriate.
-/

@[expose] public section
