/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.TruncLE

/-!
# Strict support and lower truncation restriction

This leaf owns the shape-independent comparison between a lower truncation and restriction of a
complex strictly supported on the embedded degrees.  Specialized embeddings such as natural
chain degrees consume the instance without owning it.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- For a complex strictly supported in the image of a lower truncation, the canonical map from
the truncation to its restriction is an isomorphism of complexes. -/
noncomputable instance truncLEToRestrictionIsIso
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
    [HasZeroObject C] [CategoryWithHomology C] [K.IsStrictlySupported e] :
    IsIso (K.truncLE'ToRestriction e) := sorry

end HomologicalComplex

