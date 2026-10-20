/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality.Iso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of canonical bounded-above left-derived degrees

This file specializes model-independent degree functoriality to canonical bounded-above total
left-derived functors.  It also records compatibility with the degree-zero comparison to the
underived functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

namespace degree

/-- A natural transformation of additive functors induces a transformation between each
canonical left-derived degree. -/
@[stacks 015A "naturality of canonical bounded-above left-derived degrees"]
noncomputable abbrev map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (i : ℤ) :
    Bounded.degree F i ⟶ Bounded.degree G i :=
  LeftDerived.degree.map (Bounded.map τ) i

/-- The canonical action on left-derived degrees preserves identity transformations. -/
@[simp, stacks 015A "identity on canonical bounded-above left-derived degrees"]
theorem map_id
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (i : ℤ) :
    map (𝟙 F) i = 𝟙 (Bounded.degree F i) := sorry

/-- The canonical action on left-derived degrees preserves composition. -/
@[simp, stacks 015A "composition on canonical bounded-above left-derived degrees"]
theorem map_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [H.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of additive functors induces an isomorphism between each canonical
left-derived degree. -/
@[stacks 015A "isomorphisms of canonical bounded-above left-derived degrees"]
noncomputable abbrev mapIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    Bounded.degree F i ≅ Bounded.degree G i :=
  LeftDerived.degree.mapIso (Bounded.mapIso e) i

/-- The forward map of the canonical degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_hom
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse map of the canonical degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_inv
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

end degree

/-- The canonical comparison `L⁰F ⟶ F` is natural in the additive functor. -/
@[reassoc, stacks 015A "naturality of the canonical left-derived degree-zero comparison"]
theorem zero_naturality
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) :
    degree.map τ 0 ≫ zero G = zero F ≫ τ := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
