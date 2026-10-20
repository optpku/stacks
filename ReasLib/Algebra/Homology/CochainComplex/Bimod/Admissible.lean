module

public import ReasLib.Algebra.Homology.CochainComplex.Admissible
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
public import ReasLib.CategoryTheory.Monoidal.Bimod.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Admissible sequences of modules over cochain monoids

Admissibility forgets the differential while retaining the action of the coefficient monoid.  It
therefore lives on right module objects, rather than on their underlying cochain complexes.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable {A : Mon (CochainComplex C ℤ)}

/-- Forgetting the differential transports right modules over a cochain monoid to right modules
over its underlying graded monoid. -/
@[stacks 0FSC "graded-forgetful right module functor"]
noncomputable def forgetToGradedRight (A : Mon (CochainComplex C ℤ)) :
    RightModule A ⥤
      RightModule ((CochainComplex.forgetToGraded C).mapMon.obj A) :=
  (CochainComplex.forgetToGraded C).mapRightModule A

/-- Forgetting the differential transports left modules over a cochain monoid to left modules
over its underlying graded monoid. -/
@[stacks 0FSC "graded-forgetful left module functor"]
noncomputable def forgetToGradedLeft (A : Mon (CochainComplex C ℤ)) :
    LeftModule A ⥤
      LeftModule ((CochainComplex.forgetToGraded C).mapMon.obj A) :=
  (CochainComplex.forgetToGraded C).mapLeftModule A

variable [Preadditive (CochainComplex C ℤ)]
variable [MonoidalPreadditive (CochainComplex C ℤ)]

/-- A short exact sequence of right modules over a cochain monoid is admissible when it splits
after forgetting the differential while retaining the graded monoid action. -/
@[stacks 0FSC "admissible short exact sequence of cochain-monoid modules"]
abbrev IsAdmissibleShortExact (S : ShortComplex (RightModule A)) : Prop :=
  _root_.IsAdmissibleShortExact (forgetToGradedRight A) S

/-- Admissibility is short exactness together with splitness of both maps after forgetting the
differential and retaining the graded monoid action. -/
theorem isAdmissibleShortExact_iff (S : ShortComplex (RightModule A)) :
    IsAdmissibleShortExact S ↔
      S.ShortExact ∧
        IsSplitMono ((forgetToGradedRight A).map S.f) ∧
        IsSplitEpi ((forgetToGradedRight A).map S.g) := sorry

end CategoryTheory.Bimod

end
