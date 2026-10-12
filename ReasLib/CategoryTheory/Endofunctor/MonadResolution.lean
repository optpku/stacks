/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Evaluation

/-!
# Cosimplicial resolutions of monads

Compatibility facade for the reusable monad-resolution API. Downstream files should import the
narrowest semantic leaf they use:

* `Realization` for witnesses, degree transports, splitting, and generic coaugmentations;
* `Generators` for raw unit/multiplication presentations and generator-code evaluation;
* `Construction` for the canonical resolution, monad functoriality, and realization isomorphisms;
* `Augmentation` for augmented resolutions and their functorial comparisons;
* `Evaluation` for pointwise evaluated resolutions.
-/
