/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Map
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Functorial

/-!
# Functorial API for Localizer-Morphism Resolutions

Convenience import for the direction-specific model, computation, naturality, and cross-object
map APIs of right and left resolutions.  Applications using only one direction should import its
leaf directly.
-/
