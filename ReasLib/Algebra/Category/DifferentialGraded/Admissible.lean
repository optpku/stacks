/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Equivalence
public import ReasLib.CategoryTheory.ShortComplex.Admissible
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissibility in a differential graded category

Admissibility is splitness after forgetting the differential but retaining every degree-zero
morphism.  This file supplies the intrinsic `Comp` predicates and morphism properties used by
the abstract cone and triangulation APIs.
-/

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory
namespace Comp

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]

/-- A closed degree-zero morphism is admissibly monic when it becomes split monic after
forgetting closedness. -/
@[stacks 09JT "admissible monomorphism in a differential graded category"]
abbrev IsAdmissibleMono {X Y : Comp R A} (f : X ⟶ Y) : Prop :=
  _root_.IsAdmissibleMono (forgetToDegreeZero : Comp R A ⥤ DegreeZero R A) f

/-- A closed degree-zero morphism is admissibly epic when it becomes split epic after
forgetting closedness. -/
@[stacks 09JT "admissible epimorphism in a differential graded category"]
abbrev IsAdmissibleEpi {X Y : Comp R A} (f : X ⟶ Y) : Prop :=
  _root_.IsAdmissibleEpi (forgetToDegreeZero : Comp R A ⥤ DegreeZero R A) f

/-- Admissibly monic closed morphisms as a reusable morphism property. -/
def admissibleMonomorphisms : MorphismProperty (Comp R A) :=
  fun _ _ f ↦ IsAdmissibleMono f

/-- Admissibly epic closed morphisms as a reusable morphism property. -/
def admissibleEpimorphisms : MorphismProperty (Comp R A) :=
  fun _ _ f ↦ IsAdmissibleEpi f

end Comp
end DifferentialGradedCategory

namespace CategoryTheory.ShortComplex

open DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]

/-- A graded splitting of a short complex consists of splitting maps which need not commute
with the differential. -/
@[stacks 09JT "graded splitting in a differential graded category"]
abbrev GradedSplitting (S : ShortComplex (Comp R A)) : Type w :=
  (S.map (Comp.forgetToDegreeZero : Comp R A ⥤ DegreeZero R A)).Splitting

/-- A short complex is admissibly short exact when its underlying degree-zero sequence is
split. -/
@[stacks 09JT "admissibly exact short complex in a differential graded category"]
def IsAdmissibleShortExact (S : ShortComplex (Comp R A)) : Prop :=
  Nonempty S.GradedSplitting

/-- A displayed graded splitting gives admissibility of its short complex. -/
theorem isAdmissibleShortExact_of_gradedSplitting
    {S : ShortComplex (Comp R A)} (sigma : S.GradedSplitting) :
    S.IsAdmissibleShortExact := sorry

/-- Admissibility of a short complex is equivalent to the existence of a graded splitting. -/
theorem isAdmissibleShortExact_iff (S : ShortComplex (Comp R A)) :
    S.IsAdmissibleShortExact ↔ Nonempty S.GradedSplitting := sorry

end CategoryTheory.ShortComplex

open DifferentialGradedCategory
