/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictPseudofunctor.Inverse
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Extend.Functor
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Restrict.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence over a discrete fibration

Extension and restriction are mutually inverse up to biequivalence before any
topology or stack condition is introduced. The construction applies to every
discrete fibration `G : B ⥤ C`; the canonical slice projection is one
specialization and gives the reusable owner behind localization for stacks.
-/

@[expose] public section

universe uB uC vB vC

namespace CategoryTheory.FiberedCategoryOver.Slice

open Bicategory
open scoped CategoryTheory.Bicategory

variable {B : Type uB} {C : Type uC}
variable [Category.{vB} B] [Category.{vC} C]

namespace Extend.restrict

/-- Extension and restriction along a discrete fibration are mutually inverse on objects,
`1`-morphisms, and `2`-morphisms. -/
theorem isStrictInverse (G : B ⥤ C) [G.IsDiscreteFibration] :
    StrictPseudofunctor.IsStrictInverse (Extend.functor G) (Restrict.functor G) := by
  have rightObj (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
      (Extend.functor G).obj ((Restrict.functor G).obj X) = X := by
    rcases X with ⟨⟨⟨S, cS, p⟩, hp⟩, ⟨⟨q, hq⟩, hq'⟩⟩
    change @Functor S cS B _ at q
    change q ⋙ G = p at hq
    subst p
    rfl
  have rightMap {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)} (F : X ⟶ Y) :
      (Extend.functor G).map ((Restrict.functor G).map F) ≍ F := by
    rcases X with ⟨⟨⟨S, cS, p⟩, hp⟩, ⟨⟨q, hq⟩, hq'⟩⟩
    rcases Y with ⟨⟨⟨T, cT, r⟩, hr⟩, ⟨⟨s, hs⟩, hs'⟩⟩
    change @Functor S cS B _ at q
    change q ⋙ G = p at hq
    subst p
    change @Functor T cT B _ at s
    change s ⋙ G = r at hs
    subst r
    apply heq_of_eq
    apply StrictSlice.Hom.ext
    rfl
  refine ⟨(fun _ ↦ rfl), (fun {_ _} _ ↦ HEq.rfl), (fun {_ _} {_ _} _ ↦ HEq.rfl),
    rightObj, @rightMap, ?_⟩
  intro X Y F H eta
  have cell_ext : ∀ {F' H' : X ⟶ Y} (theta : F' ⟶ H'),
      F' ≍ F → H' ≍ H →
      StrictSlice.Hom₂.hom theta ≍ StrictSlice.Hom₂.hom eta → theta ≍ eta := by
    intro F' H' theta hF hH htheta
    cases hF
    cases hH
    exact heq_of_eq (StrictSlice.Hom₂.ext (eq_of_heq htheta))
  rcases X with ⟨⟨⟨S, cS, p⟩, hp⟩, ⟨⟨q, hq⟩, hq'⟩⟩
  rcases Y with ⟨⟨⟨T, cT, r⟩, hr⟩, ⟨⟨s, hs⟩, hs'⟩⟩
  change @Functor S cS B _ at q
  change q ⋙ G = p at hq
  subst p
  change @Functor T cT B _ at s
  change s ⋙ G = r at hs
  subst r
  exact cell_ext _ (rightMap F) (rightMap H) HEq.rfl

/-- Restricting an extension along a discrete fibration recovers the original fibred-category
object. -/
@[simp]
theorem obj (G : B ⥤ C) [G.IsDiscreteFibration]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    (Restrict.functor G).obj ((Extend.functor G).obj X) = X := by
  rfl

/-- Restricting an extended morphism recovers the original morphism up to the endpoint
transports recorded by heterogeneous equality. -/
@[simp]
theorem map (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    (Restrict.functor G).map ((Extend.functor G).map F) ≍ F := by
  rfl

/-- Restricting an extended `2`-morphism recovers the original `2`-morphism up to endpoint
transport. -/
@[simp]
theorem map₂ (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (Restrict.functor G).map₂ ((Extend.functor G).map₂ eta) ≍ eta := by
  rfl

end Extend.restrict

namespace Restrict.extend

/-- Extending a restriction along a discrete fibration recovers the original strict-slice
object. -/
@[simp]
theorem obj (G : B ⥤ C) [G.IsDiscreteFibration]
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    (Extend.functor G).obj ((Restrict.functor G).obj X) = X := by
  exact (Extend.restrict.isStrictInverse G).right_obj X

/-- Extending a restricted strict-slice morphism recovers the original morphism up to endpoint
transport. -/
@[simp]
theorem map (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)} (F : X ⟶ Y) :
    (Extend.functor G).map ((Restrict.functor G).map F) ≍ F := by
  exact (Extend.restrict.isStrictInverse G).right_map F

/-- Extending a restricted strict-slice `2`-morphism recovers the original `2`-morphism up to
endpoint transport. -/
@[simp]
theorem map₂ (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (Extend.functor G).map₂ ((Restrict.functor G).map₂ eta) ≍ eta := by
  exact (Extend.restrict.isStrictInverse G).right_map₂ eta

end Restrict.extend

namespace Extend

/-- Extension along a discrete fibration is canonically a biequivalence. -/
instance isBiequivalence (G : B ⥤ C) [G.IsDiscreteFibration] :
    Pseudofunctor.IsBiequivalence
      (Extend.functor G).toPseudofunctor := by
  exact (Extend.restrict.isStrictInverse G).leftIsBiequivalence

end Extend

namespace Restrict

/-- Restriction along a discrete fibration is canonically a biequivalence. -/
instance isBiequivalence (G : B ⥤ C) [G.IsDiscreteFibration] :
    Pseudofunctor.IsBiequivalence
      (Restrict.functor G).toPseudofunctor := by
  exact (Extend.restrict.isStrictInverse G).rightIsBiequivalence

end Restrict

end CategoryTheory.FiberedCategoryOver.Slice
