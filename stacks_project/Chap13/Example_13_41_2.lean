module

import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov.Functor.Evaluation
import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov.Stage.Comparison
import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Colimit
import StacksCheckRecall

@[expose] public section

/-!
# Example 13.41.2

The neutral brutal-truncation API owns the stage complexes and their successive short exact
sequences.  Its derived specialization packages these triangles as a functorial Postnikov tower,
while the colimit leaf identifies the infinite tower with the original complex.
-/

/- Example 13.41.2: consecutive brutal truncations form the canonical short exact row used for
the Postnikov triangle. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Trunc.Step.shortExact

/- Example 13.41.2: a complex concentrated in degrees at most zero has a canonical sequential
Postnikov tower in its derived category. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.tower

/- Example 13.41.2: a cochain map induces a morphism of the canonical Postnikov towers. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.map

/- Example 13.41.2: the triangle constructed from the short exact truncation row is canonically
isomorphic to the normalized stage triangle stored in the Postnikov tower. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Stage.towerTriangleIso

/- Functorial companion: complexes with their fixed strict upper bound form the natural domain
of the canonical brutal Postnikov-tower functor. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor

/- Example 13.41.2: every finite prefix is a finite Postnikov system on the reversed term row. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite.system

/- Example 13.41.2: tower morphisms restrict functorially to finite Postnikov systems. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite.map

/- Functorial companion: finite restriction lands directly in the category of a base object
together with a finite Postnikov system. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite.functor

/- Functorial companion: evaluating a triangle after finite restriction is evaluation of the
corresponding stage of the underlying sequential Postnikov tower. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite.functor_comp_triangle

/- Example 13.41.2: the canonical cocone from the brutal truncation diagram to the original
complex satisfies the colimit universal property. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Trunc.isColimit

/- Functorial companion: chosen colimits of brutal truncation diagrams are naturally isomorphic
to the original complexes. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Trunc.Colimit.Comparison.natIso

/- Example 13.41.2: after passage to the derived category, the original complex is a homotopy
colimit of the brutal truncation sequence. -/
@[stacks 0D8Z] #check
  @CategoryTheory.CochainComplex.Brutal.Trunc.Colimit.Derived.isOf
