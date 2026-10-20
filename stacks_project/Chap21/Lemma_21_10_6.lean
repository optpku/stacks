/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/- Lemma 21.10.6 (Tag 03AZ): a covering family admits a coefficient-natural Cech spectral
sequence whose second page is Cech cohomology of the cohomology presheaves and whose abutment is
site cohomology over the covered object. -/

@[stacks 03AZ "existence of a Cech spectral-sequence system"]
#check @CategoryTheory.Cech.spectralSequenceSystem_nonempty

#check @CategoryTheory.Cech.pageTwoFunctor
#check @CategoryTheory.Cech.pageTwoFunctor_obj
#check @CategoryTheory.Cech.abutmentFunctor
#check @CategoryTheory.Cech.pageTwoSource
#check @CategoryTheory.Cech.SpectralSequenceSystem
#check @CategoryTheory.Cech.SpectralSequenceSystem.pageTwoComparison
#check @CategoryTheory.Cech.SpectralSequenceSystem.converges
#check @CategoryTheory.Cech.SpectralSequenceSystem.pageTwoIso
#check @CategoryTheory.Cech.SpectralSequenceSystem.pageTwo_naturality
#check @CategoryTheory.Cech.SpectralSequenceSystem.pageTwo_naturality_inv
#check @CategoryTheory.Cech.SpectralSequenceSystem.converges_app
#check @CategoryTheory.Cech.SpectralSequenceSystem.abuts_app
