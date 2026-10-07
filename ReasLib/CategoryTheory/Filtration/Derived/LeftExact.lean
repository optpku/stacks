module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import ReasLib.CategoryTheory.Filtration.LeftExact
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left-Exact Functors on Bounded-Below Finite Filtered Categories

This module connects the neutral finite-filtration map functor to bounded-below homotopy and
derived categories. The homotopy functor, the existence condition for its right derived functor,
the derived functor itself, and its unit are exposed as separate reusable declarations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- Equation 13.26.13.1 (`05TZ`): the bounded-below homotopy functor induced by applying a
left-exact functor to finite filtered objects. -/
@[stacks 05TZ]
noncomputable def homotopy (T : A ⥤ₗ B) :
    HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤
      HomotopyCategory.Plus (FilteredObject.Finite.category B) :=
  (FilteredObject.Finite.mapFunctor T.obj).mapHomotopyCategoryPlus

/-- Objectwise computation for the bounded-below homotopy functor induced by `T`. -/
@[simp]
theorem homotopy_obj_obj (T : A ⥤ₗ B)
    (K : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    ((homotopy T).obj K).obj =
      ((FilteredObject.Finite.mapFunctor T.obj).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded-below homotopy functor induced by `T`. -/
@[simp]
theorem homotopy_map_hom (T : A ⥤ₗ B)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    ((homotopy T).map f).hom =
      ((FilteredObject.Finite.mapFunctor T.obj).mapHomotopyCategory
        (ComplexShape.up ℤ)).map f.hom := sorry

variable [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]
variable (T : A ⥤ₗ B)
variable (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B)

/-- The existence condition for the bounded-below filtered right derived functor of `T`. -/
abbrev Has : Prop :=
  Functor.HasRightDerivedFunctor
    (homotopy T ⋙ Plus.Quotient.functor B hB)
    (Plus.QuasiIso A)

/-- Enough injectives provide the bounded-below finite filtered right-derived functor.

This instance is the standard 015S entry point.  The abstract `Has` hypothesis remains the
appropriate interface for callers using a different derivability argument. -/
@[stacks 015S "existence of the finite filtered right-derived functor"]
instance hasOfEnoughInjectives [EnoughInjectives A] : Has T hB := sorry

/-- Equation 13.26.13.2 (`015S`): the bounded-below filtered right derived functor of a
left-exact functor. -/
@[stacks 015S]
noncomputable def functor [Has T hB] :
    Plus.Category A hA ⥤ Plus.Category B hB :=
  Functor.totalRightDerived
    (homotopy T ⋙ Plus.Quotient.functor B hB)
    (Plus.Quotient.functor A hA) (Plus.QuasiIso A)

/-- The canonical factorization from the homotopy-level source to its filtered right derived
functor. -/
noncomputable def unit [Has T hB] :
    homotopy T ⋙ Plus.Quotient.functor B hB ⟶
      Plus.Quotient.functor A hA ⋙ functor T hA hB :=
  Functor.totalRightDerivedUnit
    (homotopy T ⋙ Plus.Quotient.functor B hB)
    (Plus.Quotient.functor A hA) (Plus.QuasiIso A)

/-- The canonical `functor` and `unit` form a right-derived-functor package.

Keeping this as a named instance lets downstream constructions use the universal-property API
without unfolding the bounded filtered definitions. -/
@[stacks 015S "filtered left-exact right-derived functor instance"]
instance isRightDerivedFunctor [Has T hB] :
    (functor T hA hB).IsRightDerivedFunctor (unit T hA hB) (Plus.QuasiIso A) := sorry

/-- The left-exact filtered unit is the canonical total right-derived unit. -/
@[simp, stacks 015S "filtered left-exact right-derived unit computation"]
theorem unit_eq_totalRightDerivedUnit [Has T hB] :
    unit T hA hB =
      Functor.totalRightDerivedUnit
        (homotopy T ⋙ Plus.Quotient.functor B hB)
        (Plus.Quotient.functor A hA) (Plus.QuasiIso A) := sorry

/-- The universal-property factorization attached to the canonical filtered right-derived unit. -/
@[reassoc (attr := simp), stacks 015S "filtered left-exact right-derived unit factorization"]
theorem unit_fac [Has T hB]
    (G : Plus.Category A hA ⥤ Plus.Category B hB)
    (β : homotopy T ⋙ Plus.Quotient.functor B hB ⟶
      Plus.Quotient.functor A hA ⋙ G) :
    unit T hA hB ≫
        Functor.whiskerLeft (Plus.Quotient.functor A hA)
          ((functor T hA hB).rightDerivedDesc
            (unit T hA hB) (Plus.QuasiIso A) G β) = β := sorry

/-- Component form of `unit_fac` at a bounded-below filtered homotopy object. -/
@[simp, stacks 015S "filtered left-exact right-derived unit factorization component"]
theorem unit_fac_app [Has T hB]
    (G : Plus.Category A hA ⥤ Plus.Category B hB)
    (β : homotopy T ⋙ Plus.Quotient.functor B hB ⟶
      Plus.Quotient.functor A hA ⋙ G)
    (K : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    (unit T hA hB).app K ≫
        ((functor T hA hB).rightDerivedDesc
          (unit T hA hB) (Plus.QuasiIso A) G β).app
          ((Plus.Quotient.functor A hA).obj K) = β.app K := sorry

end CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact
