/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.CosimplicialResolution.Contraction

/-!
# Cosimplicial resolutions associated to adjunctions

Compatibility facade for the reusable adjunction-resolution API. Downstream files should import
`Construction` for canonical resolutions and uncontracted evaluations, or `Contraction` for the
counit-induced extra codegeneracies and structured homotopy equivalences.
-/
