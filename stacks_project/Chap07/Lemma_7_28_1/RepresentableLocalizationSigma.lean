module

public import ReasLib.CategoryTheory.Functor.Over.LeftKanExtension

/-!
# Legacy compatibility module for Lemma 7.28.1

The left-Kan-extension sigma calculation is owned by
`CategoryTheory.Over.Forget.LeftKanExtension` in ReasLib.  This module remains only so legacy
module imports do not reintroduce a chapter-local implementation.
-/

@[expose] public section

#check @CategoryTheory.Over.Forget.LeftKanExtension.objIsoSigma
#check @CategoryTheory.Over.Forget.LeftKanExtension.fiberIsoMk
#check @CategoryTheory.Over.Forget.LeftKanExtension.fiberIso
#check @CategoryTheory.Over.Forget.LeftKanExtension.fiberIso.hom_heq_snd
