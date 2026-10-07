module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
import StacksCheckRecall

/-!
# Lemma 25.5.2 compatibility

The Čech complex and cohomology of a fixed-target hypercovering are owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology`. This compatibility module retains the
chapter import path and source label.
-/

/-
Lemma 25.5.2: for an injective abelian sheaf, a fixed-target hypercovering has degree-zero
Čech cohomology isomorphic to its sections over the target and vanishing positive Čech
cohomology.
-/
@[stacks 01GW "degree zero"] #check
  @CategoryTheory.Hypercovering.Cech.cohomology_zero_isomorphic_sections_of_injective

/- Lemma 25.5.2 [stacks 01GW], positive-degree vanishing clause. -/
@[stacks 01GW "positive degrees"] #check
  @CategoryTheory.Hypercovering.Cech.cohomology_isZero_of_injective_pos

#check CategoryTheory.HypercoveringOf.Cech.sectionsFunctor
#check CategoryTheory.Hypercovering.Cech.complex
#check CategoryTheory.Hypercovering.Cech.cohomology
