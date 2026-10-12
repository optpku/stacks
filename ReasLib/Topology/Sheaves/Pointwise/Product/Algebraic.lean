/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
public import ReasLib.Topology.Sheaves.Pointwise.Product

/-!
# Algebraic pointwise product sheaves

This module supplies convenience forms of the pointwise-product sheaf theorem for categories
with the canonical concrete forgetful functor.  The generic construction remains in
`Pointwise.Product`, so users that carry a nonstandard algebraic functor do not acquire the
standard-instance import burden.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace TopCat.Presheaf.PointwiseProduct

variable {X : TopCat.{w}} {C : Type v} [Category.{w} C]

/-- The pointwise product presheaf is a sheaf when `C` uses its canonical underlying-type
functor. This is the convenient form for standard bundled algebraic categories. -/
theorem isSheaf_of_forget {FC : C → C → Type w} {CC : C → Type w}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
    (A : X → C) [IsAlgebraicStructure C (CategoryTheory.forget C)] :
    (presheaf A).IsSheaf := sorry

end TopCat.Presheaf.PointwiseProduct

end
