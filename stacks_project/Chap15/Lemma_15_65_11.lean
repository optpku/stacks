/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction
import StacksCheckRecall

/-!
# Lemma 15.65.11

@stack 064Z

Restriction of scalars preserves and reflects `m`-pseudo-coherence and pseudo-coherence when the
restricted regular module is pseudo-coherent.
-/

@[stacks 064Z "restriction and homology"]
#check @CategoryTheory.ModuleCat.RestrictScalars.homologyIso

@[stacks 064Z "restriction reflects zero objects"]
#check @CategoryTheory.ModuleCat.RestrictScalars.isZero_of_obj

@[stacks 064Z "Lemma 15.65.11 (1), m-pseudo-coherence under restriction"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.iff_restrictScalars

@[stacks 064Z "Lemma 15.65.11 (2), pseudo-coherence under restriction"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.iff_restrictScalars
