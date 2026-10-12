/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits.Coproduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits.Product

/-!
# Limits in the homotopy category of differential graded modules

Products and coproducts in the intrinsic homotopy category of right differential graded modules
are represented by the corresponding constructions before passage to homotopy classes.  As in
mathlib's concrete module limits, the ambient carrier universe contains the diagram universe.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Homotopy

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, x} R)

/-- Lemma 22.5.4 (1) (09JR): the homotopy category of right DG `A`-modules has
arbitrary coproducts. -/
@[stacks 09JR "coproducts in the homotopy category of differential graded modules"]
instance hasCoproducts :
    HasCoproducts.{v} (K R (DifferentialGradedModule.{u, max v w} A)) := sorry

/-- Lemma 22.5.4 (2) (09JR): the homotopy category of right DG `A`-modules has
arbitrary products. -/
@[stacks 09JR "products in the homotopy category of differential graded modules"]
instance hasProducts :
    HasProducts.{v} (K R (DifferentialGradedModule.{u, max v w} A)) := sorry

/-- Passage from right DG `A`-modules to their homotopy category preserves coproducts. -/
@[stacks 09JR "passage to the homotopy category preserves coproducts"]
instance toKPreservesCoproducts (ι : Type v) :
    PreservesColimitsOfShape (Discrete ι)
      (DifferentialGradedModule.toK.{u, max v w} A) := sorry

/-- Passage from right DG `A`-modules to their homotopy category preserves products. -/
@[stacks 09JR "passage to the homotopy category preserves products"]
instance toKPreservesProducts (ι : Type v) :
    PreservesLimitsOfShape (Discrete ι)
      (DifferentialGradedModule.toK.{u, max v w} A) := sorry

end DifferentialGradedModule.Homotopy
