/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.NatTrans.IsIso
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizing Generators

This module records the generation hypothesis used to extend a property from a
family of objects to an entire pretriangulated category.  Unlike orthogonal or
weak generation, localizing generation explicitly controls properties closed
under retracts, distinguished triangles, and arbitrary coproducts.
-/

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An object property is localizing when it is stable under retracts and distinguished
triangles and is closed under arbitrary coproducts. The closure witnesses are bundled as an
explicit proposition rather than installed as argument-dependent local instances. -/
def IsLocalizing (P : ObjectProperty C) : Prop :=
  P.IsStableUnderRetracts ∧ P.IsTriangulated ∧
    ∀ I : Type (max u v), P.IsClosedUnderColimitsOfShape (Discrete I)

/-- The least localizing object property containing `P`, characterized by its elimination rule
against every localizing object property containing `P`. -/
def localizingClosure (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∀ Q : ObjectProperty C, P ≤ Q → Q.IsLocalizing → Q X

/-- Every object of `P` belongs to its localizing closure. -/
theorem le_localizingClosure (P : ObjectProperty C) :
    P ≤ P.localizingClosure := sorry

/-- The localizing closure of `P` is contained in every localizing property containing `P`. -/
theorem localizingClosure_le {P Q : ObjectProperty C} (hPQ : P ≤ Q)
    (hQ : Q.IsLocalizing) :
    P.localizingClosure ≤ Q := sorry

/-- The localizing closure is itself localizing. -/
theorem localizingClosure_isLocalizing (P : ObjectProperty C) :
    P.localizingClosure.IsLocalizing := sorry

/-- A localizing object property is unchanged by taking its localizing closure. -/
theorem localizingClosure_eq_self (P : ObjectProperty C) (hP : P.IsLocalizing) :
    P.localizingClosure = P := sorry

/-- An object property is a localizing generator when its localizing closure is the whole
category. -/
def IsLocalizingGenerator (P : ObjectProperty C) : Prop :=
  P.localizingClosure = ⊤

namespace IsLocalizingGenerator

variable {P Q : ObjectProperty C}

/-- A localizing generator proves every localizing property which contains the generators. -/
theorem holds (hP : P.IsLocalizingGenerator) (hPQ : P ≤ Q)
    (hQ : Q.IsLocalizing) (X : C) :
    Q X := sorry

/-- A localizing property which contains a localizing generator is the property of all objects. -/
theorem eq_top (hP : P.IsLocalizingGenerator) (hPQ : P ≤ Q)
    (hQ : Q.IsLocalizing) :
    Q = ⊤ := sorry

end IsLocalizingGenerator

end CategoryTheory.ObjectProperty

namespace CategoryTheory.NatTrans

variable {C : Type u} {D : Type*} [Category.{v} C] [Category D]
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {F G : C ⥤ D} (α : F ⟶ G)

/-- Membership in a localizing closure propagates invertibility of a natural-transformation
component from the generating family to the selected object. This is the pointwise induction
principle used for semi-free and cellular filtrations. -/
theorem isIso_app_of_mem_localizingClosure
    (P : ObjectProperty C) (X : C) (hX : P.localizingClosure X)
    (h_generator : P ≤ isomorphismLocus α)
    (h_localizing : (isomorphismLocus α).IsLocalizing) :
    IsIso (α.app X) := sorry

/-- A localizing generating family contained in the isomorphism locus of a natural
transformation upgrades componentwise invertibility to invertibility of the whole natural
transformation. Closure assumptions are explicit because they depend on the particular
transformation rather than on the ambient category. -/
theorem isIso_of_localizingGenerator
    (P : ObjectProperty C) (h_generate : P.IsLocalizingGenerator)
    (h_generator : P ≤ isomorphismLocus α)
    (h_localizing : (isomorphismLocus α).IsLocalizing) :
    IsIso α := sorry

end CategoryTheory.NatTrans
