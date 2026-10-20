/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
