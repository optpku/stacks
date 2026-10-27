/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Coface criteria for cartesian sheaves on simplicial sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- A sheaf of sets on a simplicial total site is cartesian if and only if every coface comparison
is an isomorphism. -/
theorem Sheaf.isCartesian_iff_delta (F : Sheaf (topology C J) (Type w)) :
    IsCartesian C J F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (transition C J (SimplexCategory.δ j) F) := sorry

/-- A sheaf of sets whose coface comparisons are isomorphisms is cartesian. -/
instance Sheaf.instIsCartesian_of_isIso_delta (F : Sheaf (topology C J) (Type w))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (transition C J (SimplexCategory.δ j) F)] :
    IsCartesian C J F := sorry

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

/-- A sheaf of abelian groups on a simplicial total site is cartesian if and only if every coface
comparison is an isomorphism. -/
theorem abelian_isCartesian_iff_delta (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    Abelian.IsCartesian C J F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (abelianTransition C J (SimplexCategory.δ j) F) := sorry

/-- A sheaf of abelian groups whose coface comparisons are isomorphisms is cartesian. -/
instance instAbelianIsCartesian_of_isIso_delta
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (abelianTransition C J (SimplexCategory.δ j) F)] :
    Abelian.IsCartesian C J F := sorry

section AbelianDerived

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- An unbounded derived abelian sheaf on a simplicial total site is cartesian if and only if
every coface comparison is an isomorphism. -/
theorem AbelianDerived.isCartesian_iff_delta
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian C J K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (derivedTransition C J (SimplexCategory.δ j) K) := sorry

/-- An object of `D(C_total)` whose coface comparisons are isomorphisms is cartesian. -/
instance AbelianDerived.instIsCartesian_of_isIso_delta
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (derivedTransition C J (SimplexCategory.δ j) K)] :
    AbelianDerived.IsCartesian C J K := sorry

end AbelianDerived

end Abelian

end CategoryTheory.SimplicialSites
