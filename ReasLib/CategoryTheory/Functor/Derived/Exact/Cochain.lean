module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.Cochain

@[expose] public section

/-!
# Cochain-Level Derivation of Exact Functors

An exact functor induces a functor on derived categories directly from its
action on cochain complexes. This leaf records the corresponding left- and
right-derived universal properties.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Exact.Cochain

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The derived-category functor induced by an exact functor is its
cochain-level right derived functor. -/
@[stacks 015F]
noncomputable instance isRightDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsRightDerivedFunctor
      F.mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

/-- The cochain-level localization of an exact functor admits the functor induced on derived
categories as a right derived functor. The higher priority selects this exact model over
resolution-based fallback instances when both apply. -/
@[stacks 015F]
noncomputable instance (priority := 1100) hasRightDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Derived.Cochain.toDerived F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

end CategoryTheory.Functor.RightDerived.Exact.Cochain

namespace CategoryTheory.Functor.LeftDerived.Exact.Cochain

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The derived-category functor induced by an exact functor is its
cochain-level left derived functor. -/
@[stacks 015F]
noncomputable instance isLeftDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsLeftDerivedFunctor
      F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

/-- The cochain-level localization of an exact functor admits the functor induced on derived
categories as a left derived functor. -/
@[stacks 015F]
noncomputable instance (priority := 1100) hasLeftDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Derived.Cochain.toDerived F).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

end CategoryTheory.Functor.LeftDerived.Exact.Cochain
