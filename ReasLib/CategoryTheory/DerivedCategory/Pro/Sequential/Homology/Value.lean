module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Diagram
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Value
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Values of bounded sequential derived pro-objects

Uniform cohomological bounds reduce essential constancy of a sequential derived tower to
essential constancy of its finitely many relevant homology towers.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped ZeroObject

universe w u v

namespace CategoryTheory.DerivedCategory.Pro.Sequential.Homology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Lemma 13.42.3 (0G3B) (1): a uniformly bounded sequential derived tower with essentially
constant homology towers has a pro-value whose homology gives the values of all degreewise
towers. -/
@[stacks 0G3B]
theorem existsValue
    (F : SequentialInverseSystem (DerivedCategory A)) (a b : ℤ)
    (hF : IsUniformlyBounded F a b)
    (hH : ∀ i ∈ Set.Icc a b,
      IsCofiltered.IsEssentiallyConstant (F ⋙ DerivedCategory.homologyFunctor A i)) :
    ∃ X : DerivedCategory A, _root_.CategoryTheory.Pro.HasValue F X ∧
      ∀ i : ℤ,
        _root_.CategoryTheory.Pro.HasValue
          (F ⋙ DerivedCategory.homologyFunctor A i)
          ((DerivedCategory.homologyFunctor A i).obj X) := sorry

/-- Lemma 13.42.3 (0G3B) (2): under uniform bounds, essential constancy of the homology towers
in the bounding interval implies essential constancy of the derived tower. -/
@[stacks 0G3B]
theorem essentiallyConstant
    (F : SequentialInverseSystem (DerivedCategory A)) (a b : ℤ)
    (hF : IsUniformlyBounded F a b)
    (hH : ∀ i ∈ Set.Icc a b,
      IsCofiltered.IsEssentiallyConstant (F ⋙ DerivedCategory.homologyFunctor A i)) :
    IsCofiltered.IsEssentiallyConstant F := sorry

/-- A uniformly bounded sequential derived tower is pro-zero when all of its homology towers in
the bounding interval have value zero. -/
theorem hasValueZero
    (F : SequentialInverseSystem (DerivedCategory A)) (a b : ℤ)
    (hF : IsUniformlyBounded F a b)
    (hH : ∀ i ∈ Set.Icc a b,
      _root_.CategoryTheory.Pro.HasValue
        (F ⋙ DerivedCategory.homologyFunctor A i) (0 : A)) :
    _root_.CategoryTheory.Pro.HasValue F (0 : DerivedCategory A) := sorry

end CategoryTheory.DerivedCategory.Pro.Sequential.Homology
