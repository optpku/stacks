/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Structure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.ConnectedComponent
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced

/-!
# Closed subschemes

Convenience import for reusable closed-subscheme infrastructure. It provides
scheme structures on prescribed closed subsets, their inverse images, reduced induced structures,
properness over a base scheme, and the reduced closed subschemes attached to
irreducible and connected components.
-/
