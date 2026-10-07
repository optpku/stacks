module

public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.GradedObject.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded-object view of finite filtered derived objects

The primary finite filtered derived associated-graded functor lands in `D(Gr(C))`.  This leaf
provides the companion view in `Gr(D(C))` and a named evaluation comparison with the direct
derived graded-piece functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

namespace Graded

/-- The graded-object-valued companion to finite derived associated graded. -/
@[stacks 05S3 "finite filtered derived graded object"]
noncomputable def functor
    (h_inverts : AssociatedGraded.Inverts C) :
    Quotient.Category C ⥤ GradedObject ℤ (DerivedCategory C) :=
  AssociatedGraded.lift C h_inverts ⋙
    GradedObject.Derived.Evaluation.functor C

/-- Evaluation of the graded-object-valued companion at `p` is canonically isomorphic to the
direct finite derived `p`-th graded-piece functor. -/
@[stacks 05S3 "finite filtered derived graded object"]
noncomputable def evalIso
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    functor C h_inverts ⋙
        (GradedObject.eval p : GradedObject ℤ (DerivedCategory C) ⥤ DerivedCategory C) ≅
      GradedPiece.lift C h_inverts p :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (GradedObject.Derived.Evaluation.compEval C p)

/-- The canonical graded-object-valued finite filtered derived functor. -/
@[stacks 05S3 "canonical finite filtered derived graded object"]
noncomputable abbrev canonicalFunctor :
    Quotient.Category C ⥤ GradedObject ℤ (DerivedCategory C) :=
  functor C (AssociatedGraded.inverts C)

/-- Evaluation of the canonical graded-object-valued functor at an integer degree. -/
@[stacks 05S3 "canonical finite filtered derived graded object"]
noncomputable abbrev canonicalEvalIso (p : ℤ) :
    canonicalFunctor C ⋙
        (GradedObject.eval p : GradedObject ℤ (DerivedCategory C) ⥤ DerivedCategory C) ≅
      GradedPiece.canonicalLift C p :=
  evalIso C (AssociatedGraded.inverts C) p

end Graded

end CategoryTheory.FilteredObject.FiniteDerived
