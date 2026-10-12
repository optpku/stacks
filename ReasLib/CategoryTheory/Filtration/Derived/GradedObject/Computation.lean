/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.GradedObject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluation of finite derived graded objects

This leaf exposes the components of the canonical comparison between evaluation of the
graded-object-valued derived functor and the direct derived graded-piece functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.Graded.Computation

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

/-- The forward component of `Graded.evalIso` is the component of the derived evaluation
comparison after applying finite associated graded. -/
@[stacks 05S3 "finite derived graded-object computation", simp]
theorem evalIso_hom_app
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) (X : Quotient.Category C) :
    (Graded.evalIso C h_inverts p).hom.app X =
      (GradedObject.Derived.Evaluation.compEval C p).hom.app
        ((AssociatedGraded.lift C h_inverts).obj X) := sorry

/-- The inverse component of `Graded.evalIso` is the inverse component of the derived evaluation
comparison after applying finite associated graded. -/
@[stacks 05S3 "finite derived graded-object computation", simp]
theorem evalIso_inv_app
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) (X : Quotient.Category C) :
    (Graded.evalIso C h_inverts p).inv.app X =
      (GradedObject.Derived.Evaluation.compEval C p).inv.app
        ((AssociatedGraded.lift C h_inverts).obj X) := sorry

/-- The forward component of the canonical graded evaluation comparison. -/
@[stacks 05S3 "canonical finite derived graded-object computation", simp]
theorem canonicalEvalIso_hom_app (p : ℤ) (X : Quotient.Category C) :
    (Graded.canonicalEvalIso C p).hom.app X =
      (GradedObject.Derived.Evaluation.compEval C p).hom.app
        ((AssociatedGraded.canonicalLift C).obj X) := sorry

/-- The inverse component of the canonical graded evaluation comparison. -/
@[stacks 05S3 "canonical finite derived graded-object computation", simp]
theorem canonicalEvalIso_inv_app (p : ℤ) (X : Quotient.Category C) :
    (Graded.canonicalEvalIso C p).inv.app X =
      (GradedObject.Derived.Evaluation.compEval C p).inv.app
        ((AssociatedGraded.canonicalLift C).obj X) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.Graded.Computation
