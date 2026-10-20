/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.LocallyInjective

@[expose] public section

/- Lemma 7.11.2 (1) (00WN): local injectivity of a morphism of sheaves of
sets is equivalent to being a monomorphism. -/
@[stacks 00WN "(1)"] #check @CategoryTheory.Sheaf.isLocallyInjective_iff_mono

/- Lemma 7.11.2 (2) (00WN): local surjectivity of a morphism of sheaves of
sets is equivalent to being an epimorphism. -/
@[stacks 00WN "(2)"] #check @CategoryTheory.Sheaf.isLocallySurjective_iff_epi

/- Lemma 7.11.2 (3) (00WN): local bijectivity of a morphism of sheaves of
sets is equivalent to being an isomorphism. -/
@[stacks 00WN "(3)"] #check @CategoryTheory.Sheaf.isLocallyBijective_iff_isIso
