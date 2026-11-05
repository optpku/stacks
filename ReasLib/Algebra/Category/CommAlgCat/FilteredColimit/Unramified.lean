/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit
public import ReasLib.RingTheory.RingHom.Unramified
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unramified maps after filtered-colimit base change

This categorical leaf is independent of the fixed-preorder direct-limit
adapters.  The finite-type hypothesis is explicit because unramifiedness of
the colimit base change does not descend to the original map by itself.

@stack 0C4F
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u v

namespace CommAlgCat.FilteredColimit.Unramified

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
variable {B C : Type u} [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Unramifiedness of the base change of a finite-type algebra map to a filtered colimit
is witnessed at one diagram object, provided the forgetful functor preserves this colimit.
The preservation hypothesis is supplied by the shared instance when `UnivLE.{v, u}` holds. -/
@[stacks 0C4F "unramified filtered-colimit descent"]
theorem exists_stage
    [PreservesColimit F (forget (CommAlgCat.{u} A))]
    (φ : B →ₐ[A] C) (hfiniteType : φ.FiniteType)
    (hunramified : RingHom.Unramified
      (Algebra.TensorProduct.map φ (AlgHom.id A (colimit F : CommAlgCat.{u} A))).toRingHom) :
    ∃ j : J, RingHom.Unramified
      (Algebra.TensorProduct.map φ (AlgHom.id A (F.obj j))).toRingHom := sorry

end CommAlgCat.FilteredColimit.Unramified
