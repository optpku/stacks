/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Linear.Endomorphism
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Equivalence
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.CategoryTheory.Pretriangulated.Tilting
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tilting objects under equivalences

This leaf transports self-orthogonality and the intrinsic tilting predicate along additive,
linear equivalences compatible with integer shifts.
-/

noncomputable section

universe uR uE vC uC vD uD

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory.Equivalence

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

section SelfOrthogonal

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- A zero-preserving, shift-compatible equivalence identifies self-orthogonal objects. -/
@[stacks 09S8 "equivalences preserve self-orthogonal objects"]
theorem isSelfOrthogonal_obj_iff (e : C ≌ D)
    [e.functor.PreservesZeroMorphisms] [e.functor.CommShift ℤ] (X : C) :
    IsSelfOrthogonal (e.functor.obj X) ↔ IsSelfOrthogonal X := sorry

end SelfOrthogonal

section Tilting

variable {R : Type uR} [CommSemiring R]
variable {E : Type uE} [Semiring E] [Algebra R E]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- An additive linear equivalence compatible with integer shifts identifies tilting objects
with the same prescribed endomorphism algebra. -/
@[stacks 09S8 "equivalences preserve tilting objects"]
theorem isTiltingFor_obj_iff (e : C ≌ D)
    [e.functor.Additive] [e.functor.Linear R]
    [e.inverse.PreservesZeroMorphisms] [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ] (X : C) :
    IsTiltingFor (R := R) (E := E) (e.functor.obj X) ↔
      IsTiltingFor (R := R) (E := E) X := sorry

/-- An additive linear equivalence sends a tilting object to a tilting object. -/
@[stacks 09S8 "forward transport of a tilting object along an equivalence"]
theorem isTiltingFor_obj (e : C ≌ D)
    [e.functor.Additive] [e.functor.Linear R]
    [e.inverse.PreservesZeroMorphisms] [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    (X : C) (hX : IsTiltingFor (R := R) (E := E) X) :
    IsTiltingFor (R := R) (E := E) (e.functor.obj X) := sorry

end Tilting

end CategoryTheory.Equivalence

namespace CategoryTheory.RLinear.TriangulatedEquivalence

variable (R : Type uR) [CommRing R]
variable {E : Type uE} [Semiring E] [Algebra R E]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Limits.HasZeroObject C] [Limits.HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]

/-- A bundled linear triangulated equivalence identifies tilting objects without requiring
downstream users to restate its stored linearity and shift instances. -/
@[stacks 09S8 "tilting objects under a linear triangulated equivalence"]
theorem isTiltingFor_obj_iff
    (e : TriangulatedEquivalence R C D) (X : C) :
    IsTiltingFor (R := R) (E := E) (e.functor.obj X) ↔
      IsTiltingFor (R := R) (E := E) X := sorry

/-- A bundled linear triangulated equivalence sends tilting objects to tilting objects. -/
@[stacks 09S8 "forward tilting transport under a linear triangulated equivalence"]
theorem isTiltingFor_obj
    (e : TriangulatedEquivalence R C D) (X : C)
    (hX : IsTiltingFor (R := R) (E := E) X) :
    IsTiltingFor (R := R) (E := E) (e.functor.obj X) := sorry

end CategoryTheory.RLinear.TriangulatedEquivalence
