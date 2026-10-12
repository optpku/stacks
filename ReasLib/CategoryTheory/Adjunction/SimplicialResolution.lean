/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Evaluation
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Realization

/-!
# Simplicial resolutions associated to adjunctions

Compatibility facade for the reusable adjunction-resolution API. Downstream files should import
the narrow semantic leaf they use:

* `Construction` for the canonical resolution, compositions, and uncontracted evaluations;
* `Contraction` for extra degeneracies and functor-level homotopy equivalences;
* `Evaluation` for pointwise resolutions and contractions;
* `Realization` for transport to arbitrary realizations of the comonad formulas.
-/
