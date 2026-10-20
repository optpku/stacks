/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.SelectedSlice
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.26.7

Selected-cover localized slices, their inverse images, and their glueing data
are reusable API owned by `Precoverage.LocalizedSlice`.
-/

@[expose] public section

/- Remark 7.26.7 (0GWL): local slices are closed under selected covers and
base change; inverse-image data then supports compatible localized glueing
data whose transitions are invertible on the selected local arrows. -/
@[stacks 0GWL "family"] #check @CategoryTheory.Precoverage.LocalizedSlice.Family

@[stacks 0GWL "base change"] #check @CategoryTheory.Precoverage.LocalizedSlice.baseChange

@[stacks 0GWL "localized sheaves"] #check @CategoryTheory.Precoverage.LocalizedSlice.Sheaf

@[stacks 0GWL "inverse image"] #check @CategoryTheory.Precoverage.LocalizedSlice.InverseImage

@[stacks 0GWL "glueing"] #check @CategoryTheory.Precoverage.LocalizedSlice.Glueing
