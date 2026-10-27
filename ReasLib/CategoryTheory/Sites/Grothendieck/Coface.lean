/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Coface criteria for cartesian sheaves on fiberwise simplicial sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : IsFiberwiseSite F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]

/-- A sheaf of sets on a fiberwise simplicial total site is cartesian if and only if every coface
comparison is an isomorphism. -/
theorem Sheaf.isCartesian_iff_delta (G : Sheaf (Grothendieck.topology F J) (Type w)) :
    Grothendieck.Sheaf.IsCartesian F J (Type w) G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.Sheaf.sheafTransition F J (Type w) (SimplexCategory.δ j) G) := sorry

variable [HasWeakSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- A sheaf of abelian groups on a fiberwise simplicial total site is cartesian if and only if
every coface comparison is an isomorphism. -/
theorem abelian_isCartesian_iff_delta (G : Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w}) :
    Grothendieck.Sheaf.IsCartesian F J AddCommGrpCat.{w} G ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.Sheaf.sheafTransition F J AddCommGrpCat.{w} (SimplexCategory.δ j) G) := sorry

variable [HasSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- An unbounded derived abelian sheaf on a fiberwise simplicial total site is cartesian if and
only if every coface comparison is an isomorphism. -/
theorem AbelianDerived.isCartesian_iff_delta
    (K : DerivedCategory (Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w})) :
    Grothendieck.AbelianDerived.IsCartesian F J K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.derivedTransition F J (SimplexCategory.δ j) K) := sorry

end CategoryTheory.Grothendieck
