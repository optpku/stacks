module

public import ReasLib.CategoryTheory.GradedObject.Instances
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived evaluation of graded objects

Evaluation at a grading degree is exact, hence induces a functor on derived categories.  This leaf
packages all evaluations into one functor valued in graded objects, avoiding repeated objectwise
`Functor where` constructions in filtered-derived applications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.GradedObject

variable {β : Type w} (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject β C)]

namespace Derived.Evaluation

/-- The degreewise derived-evaluation functor
`D(GradedObject β C) ⥤ GradedObject β (D(C))`. -/
@[stacks 05S3 "derived evaluation of graded objects"]
noncomputable def functor :
    DerivedCategory (GradedObject β C) ⥤ GradedObject β (DerivedCategory C) :=
  Functor.pi' (fun p ↦ (GradedObject.eval p).mapDerivedCategory)

/-- Evaluation at `p` after `Derived.Evaluation.functor` is the derived functor induced by
`GradedObject.eval p`. -/
@[stacks 05S3 "derived evaluation of graded objects"]
noncomputable def compEval (p : β) :
    functor C ⋙
        (GradedObject.eval p : GradedObject β (DerivedCategory C) ⥤ DerivedCategory C) ≅
      (GradedObject.eval p).mapDerivedCategory :=
  Functor.pi'CompEval (fun q ↦ (GradedObject.eval q).mapDerivedCategory) p

end Derived.Evaluation

end CategoryTheory.GradedObject
