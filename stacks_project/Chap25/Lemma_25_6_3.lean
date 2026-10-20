/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Injective
import StacksCheckRecall

/-!
# Injective coefficients on a presheaf-target hypercovering

The Cech complex and cohomology objects are shared `HypercoveringOf.Cech` API. The
`Injective` leaf exposes both clauses with the source's injective-coefficient hypothesis; its
degree-zero clause specializes the coefficient-independent theorem owned by `Augmentation`.
-/

/- Lemma 25.6.3 [stacks 09VW], degree-zero clause. -/
@[stacks 09VW "degree zero"] #check
  @CategoryTheory.HypercoveringOf.Cech.cohomology_zero_isomorphic_targetSections_of_injective

/- Lemma 25.6.3 [stacks 09VW], positive-degree vanishing clause. -/
@[stacks 09VW "positive degrees"] #check
  @CategoryTheory.HypercoveringOf.Cech.cohomology_isZero_of_injective_pos

#check @CategoryTheory.HypercoveringOf.Cech.sectionsFunctor
#check @CategoryTheory.HypercoveringOf.Cech.complex
#check @CategoryTheory.HypercoveringOf.Cech.cohomology
