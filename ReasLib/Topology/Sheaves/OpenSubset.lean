/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Opens.Inclusion
public import ReasLib.Topology.Opens.Subspace
public import ReasLib.Topology.Opens.SectionComparison

/-!
# Sheaf-level open-subspace infrastructure

This is the categorized import for open-subspace infrastructure used by sheaf modules. The
canonical owners are `TopCat.Opens.Subspace` and `TopCat.Opens.SectionComparison`; no parallel
flat namespace is exposed here.
-/
@[expose] public section

