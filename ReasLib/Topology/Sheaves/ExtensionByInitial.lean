/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.ExtensionByInitial
public import ReasLib.Topology.Presheaf.ExtensionByInitial.Properties
public import ReasLib.Topology.Sheaf.ExtensionByInitial
public import ReasLib.Topology.Sheaf.ExtensionByInitial.Presentation

/-!
# Extension by an initial object on open subspaces

This categorized import exposes the canonical presheaf and sheaf APIs for extension by an initial
object along an open-subspace inclusion. Construction and computation live under
`TopCat.Presheaf.ExtensionByInitial`; adjunction, stalk, and coefficient-specialized results live
under `TopCat.Presheaf.ExtensionByInitial.Properties` and
`TopCat.Sheaf.ExtensionByInitial.Properties`. Lower-shriek constant sheaves and their basis
presentations live under `TopCat.Sheaf.ExtensionByInitial.Constant`.

No source-facing duplicate names are provided here.
-/
