/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Functoriality.Composition

/-!
# Computations for functoriality of bundled-cospan mapping

This compatibility aggregate exposes the identity and composition strong-transformation
computations for `Bicategory.Cospan.map`. The two mathematical owners remain separate, while
clients that use the full functoriality interface need only this focused import.
-/
