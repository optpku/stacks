/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.26.1

The localized Hom-sheaf and coverwise glueing API is reusable descent
infrastructure. This Chapter 7 entry records the precise source-facing
statement through the ReasLib owner.
-/

@[expose] public section

/- Lemma 7.26.1 (04TQ): compatible morphisms between the restrictions of two
`Type`-valued sheaves to the members of a cover glue uniquely on the slice
site. -/
@[stacks 04TQ] #check @CategoryTheory.GrothendieckTopology.LocalizedHom.existsUnique_of_compatible

@[stacks 04TQ] #check @CategoryTheory.GrothendieckTopology.LocalizedHom.isSheafFor_cover

@[stacks 04TQ] #check @CategoryTheory.GrothendieckTopology.LocalizedHom.evalEquiv

@[stacks 04TQ] #check @CategoryTheory.GrothendieckTopology.LocalizedHom.coverSieve_overEquiv
