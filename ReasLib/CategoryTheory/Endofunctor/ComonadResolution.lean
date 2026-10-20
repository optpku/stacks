module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Evaluation

/-!
# Simplicial resolutions of comonads

Compatibility facade for the reusable comonad-resolution API. Downstream files should import
the narrowest semantic leaf they use:

* `Realization` for witnesses, degree transports, splitting, and generic augmentations;
* `Generators` for raw counit/comultiplication presentations and generator-code evaluation;
* `Construction` for the canonical resolution, comonad functoriality, and realization isomorphisms;
* `Augmentation` for augmented resolutions and their functorial comparisons;
* `Evaluation` for pointwise evaluated resolutions.
-/
