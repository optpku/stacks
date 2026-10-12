/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.ExtensionByInitial
public import ReasLib.Topology.Presheaf.Stalks
public import ReasLib.Topology.Presheaf.Cech
public import ReasLib.Topology.Presheaf.Flasque

/-!
# Presheaf-level constructions on topological spaces

This module aggregates presheaf-level API (constructions that do not require the sheaf condition).

- `ExtensionByInitial/`: the jₚ! functor (extension by initial object)
- `Stalks`: filtered stalk functor, stalk comparison for pullback
-/
