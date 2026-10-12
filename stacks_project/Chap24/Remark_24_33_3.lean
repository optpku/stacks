/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Remark 24.33.3 (1): once the bounded-object argument for the actual sectionwise
`QC(𝒜,d)` supplies a Brown-representability set, every contravariant cohomological functor that
takes direct sums to products is represented.  The source explicitly leaves that DG-specific
bounded-object construction for a later precise formulation, so this entry recalls the canonical
criterion instead of asserting the conclusion for an arbitrary comparison system. -/
@[stacks 0GZB] #check @BrownRepresentability.existsRepresentation

/- Remark 24.33.3 (2): the same Brown set makes an exact coproduct-preserving functor out of the
quasi-coherent subcategory a left adjoint. -/
@[stacks 0GZB "left adjoint"] #check @CategoryTheory.Functor.Brown.Set.isLeftAdjoint

/- Remark 24.33.3 (2): the right adjoint can be chosen triangulated. -/
@[stacks 0GZB "triangulated right adjoint"]
#check @CategoryTheory.Functor.Brown.Set.hasTriangulatedRightAdjoint

/- Remark 24.33.3 (3): after the actual DG section and relative-tensor comparison functors are
installed, their comparison locus has the canonical full-subcategory inclusion to which the same
Brown criterion applies. -/
#check @CategoryTheory.ObjectProperty.ι
