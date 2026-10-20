/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Iso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of canonical bounded-below right-derived degrees

This file specializes model-independent degree functoriality to canonical bounded-below total
right-derived functors.  It also records compatibility with the degree-zero comparison from the
underived functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

namespace degree

/-- A natural transformation of additive functors induces a transformation between each
canonical right-derived degree. -/
@[stacks 015A "naturality of canonical bounded-below right-derived degrees"]
noncomputable abbrev map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (i : ℤ) :
    Bounded.degree F i ⟶ Bounded.degree G i :=
  RightDerived.degree.map (Bounded.map τ) i

/-- The canonical action on right-derived degrees preserves identity transformations. -/
@[simp, stacks 015A "identity on canonical bounded-below right-derived degrees"]
theorem map_id
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (i : ℤ) :
    map (𝟙 F) i = 𝟙 (Bounded.degree F i) := sorry

/-- The canonical action on right-derived degrees preserves composition. -/
@[simp, stacks 015A "composition on canonical bounded-below right-derived degrees"]
theorem map_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of additive functors induces an isomorphism between each canonical
right-derived degree. -/
@[stacks 015A "isomorphisms of canonical bounded-below right-derived degrees"]
noncomputable abbrev mapIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    Bounded.degree F i ≅ Bounded.degree G i :=
  RightDerived.degree.mapIso (Bounded.mapIso e) i

/-- The forward map of the canonical degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_hom
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse map of the canonical degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_inv
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

end degree

/-- The canonical comparison `F ⟶ R⁰F` is natural in the additive functor. -/
@[reassoc, stacks 015A "naturality of the canonical right-derived degree-zero comparison"]
theorem zero_naturality
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) :
    τ ≫ zero G = zero F ≫ degree.map τ 0 := sorry

end CategoryTheory.Functor.RightDerived.Bounded
