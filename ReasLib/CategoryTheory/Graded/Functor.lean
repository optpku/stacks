/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Graded
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors of graded categories

The preservation-of-degree condition is separate from the graded-category owner so that users
which only need graded hom spaces do not import functorial infrastructure.
-/

@[expose] public section

namespace CategoryTheory

universe x w v u u' u''

section

variable {R : Type w} [Semiring R]
variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {C : Type u} {D : Type u'} {E : Type u''}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable [Preadditive C] [Preadditive D] [Preadditive E]
variable [GradedCategory R C ι] [GradedCategory R D ι] [GradedCategory R E ι]

namespace Functor

/-- A functor of graded categories is additive and `R`-linear, and preserves the degree of
every homogeneous morphism.

This is the reusable owner for the graded-functor structure from Definition 22.25.2. -/
@[stacks 09L3]
class Graded (ι : Type x) [DecidableEq ι] [AddMonoid ι]
    (R : Type w) [Semiring R] [GradedCategory R C ι]
    [GradedCategory R D ι] (F : C ⥤ D) : Prop extends F.Additive, Functor.Linear R F where
  /-- A homogeneous morphism remains homogeneous of the same degree after applying `F`. -/
  map_mem_homDegree {X Y : C} (i : ι) {f : X ⟶ Y}
      (hf : f ∈ GradedCategory.homDegree (R := R) X Y i) :
      F.map f ∈ GradedCategory.homDegree (R := R) (F.obj X) (F.obj Y) i

section

variable {F : C ⥤ D} [Graded ι R F]

/-- A graded functor preserves the degree of a homogeneous morphism. -/
theorem map_mem_homDegree {X Y : C} (i : ι) {f : X ⟶ Y}
    (hf : f ∈ GradedCategory.homDegree (R := R) X Y i) :
    F.map f ∈ GradedCategory.homDegree (R := R) (F.obj X) (F.obj Y) i := sorry

end

/-- The identity functor preserves the grading. -/
instance instGradedId : Graded ι R (𝟭 C) := sorry

/-- A composite of grading-preserving functors preserves the grading. -/
instance instGradedComp (F : C ⥤ D) (G : D ⥤ E) [Graded ι R F] [Graded ι R G] :
    Graded ι R (F ⋙ G) := sorry

end Functor

end

end CategoryTheory
