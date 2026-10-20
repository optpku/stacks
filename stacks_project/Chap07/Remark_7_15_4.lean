/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Presentation
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.15.4

Presentations of morphisms of topoi by sheaf-valued functors are reusable
topos API owned by `MorphismOfTopoiIn.Presentation`.
-/

@[expose] public section

/- Remark 7.15.4 (00XB): a sheaf-valued functor presents a morphism of topoi
when its target Hom-presheaves are sheaves and its reconstructed direct image
has a left-exact left adjoint. -/
@[stacks 00XB "presentation"] #check @CategoryTheory.MorphismOfTopoiIn.Presentation.Presents

@[stacks 00XB "direct image"] #check @CategoryTheory.MorphismOfTopoiIn.Presentation.directImage

@[stacks 00XB "reconstruction"] #check @CategoryTheory.MorphismOfTopoiIn.Presentation.Presents.toMorphism

@[stacks 00XB "canonical presentation"] #check @CategoryTheory.MorphismOfTopoiIn.presentation

@[stacks 00XB "comparison"] #check @CategoryTheory.MorphismOfTopoiIn.Presentation.directImageIso
