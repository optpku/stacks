module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Presheaf
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.13.2

The first-quadrant Cech spectral-sequence system and its source-facing existence theorem live in
ReasLib.  This chapter entry only recalls that reusable interface.
-/

/- Lemma 21.13.2 (079Z): a locally surjective presheaf map gives a first-quadrant spectral
sequence from cohomology over its sheafified Cech levels to cohomology over its target. -/
@[stacks 079Z]
#check @CategoryTheory.Presheaf.Cech.exists_spectralSequence

#check @CategoryTheory.Presheaf.Cech.sheafifiedNerve
#check @CategoryTheory.Presheaf.Cech.sheafifiedLevel
#check @CategoryTheory.Presheaf.Cech.pageOneFunctor
#check @CategoryTheory.Presheaf.Cech.abutmentFunctor
#check @CategoryTheory.Presheaf.Cech.SpectralSequenceSystem
#check @CategoryTheory.Presheaf.Cech.spectralSequenceSystem_nonempty
#check @CategoryTheory.Presheaf.Cech.SpectralSequenceSystem.pageOneIso
#check @CategoryTheory.Presheaf.Cech.SpectralSequenceSystem.converges_app
