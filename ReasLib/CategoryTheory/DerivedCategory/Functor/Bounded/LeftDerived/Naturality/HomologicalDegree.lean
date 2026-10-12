/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.HomologicalDegree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality.Degree
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of canonical homological left-derived degrees

This is the natural-number-indexed specialization of the canonical bounded-above left-derived
degree API.  It is the direct downstream interface for the usual functors `LₙF`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded.homologicalDegree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- A natural transformation of additive functors induces a transformation between every
canonical homological left-derived degree. -/
@[stacks 015A "naturality of canonical homological left-derived degrees"]
noncomputable abbrev map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (n : ℕ) :
    Bounded.homologicalDegree F n ⟶ Bounded.homologicalDegree G n :=
  LeftDerived.homologicalDegree.map (Bounded.map τ) n

/-- The canonical action on homological left-derived degrees preserves identities. -/
@[simp, stacks 015A "identity on canonical homological left-derived degrees"]
theorem map_id
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (n : ℕ) :
    map (𝟙 F) n = 𝟙 (Bounded.homologicalDegree F n) := sorry

/-- The canonical action on homological left-derived degrees preserves composition. -/
@[simp, stacks 015A "composition on canonical homological left-derived degrees"]
theorem map_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [H.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) (n : ℕ) :
    map (τ ≫ σ) n = map τ n ≫ map σ n := sorry

/-- An isomorphism of additive functors induces an isomorphism between every canonical
homological left-derived degree. -/
@[stacks 015A "isomorphisms of canonical homological left-derived degrees"]
noncomputable abbrev mapIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (n : ℕ) :
    Bounded.homologicalDegree F n ≅ Bounded.homologicalDegree G n :=
  LeftDerived.homologicalDegree.mapIso (Bounded.mapIso e) n

/-- The forward map of the canonical homological-degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_hom
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (n : ℕ) :
    (mapIso e n).hom = map e.hom n := sorry

/-- The inverse map of the canonical homological-degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_inv
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (n : ℕ) :
    (mapIso e n).inv = map e.inv n := sorry

end CategoryTheory.Functor.LeftDerived.Bounded.homologicalDegree
