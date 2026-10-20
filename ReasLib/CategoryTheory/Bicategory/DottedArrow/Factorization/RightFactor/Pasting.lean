/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Pasting.Basic
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Pasting.Comparison

/-!
# Pasting right-factor dotted arrows

`Pasting.Basic` owns the functor that pastes a left-factor dotted arrow with a fixed middle
dotted arrow. `Pasting.Comparison` adds the optional natural isomorphism comparing the recovered
right factor with that fixed middle arrow. Import the smallest leaf that supplies the required
level of structure; this file preserves the historical broad import path.
-/
