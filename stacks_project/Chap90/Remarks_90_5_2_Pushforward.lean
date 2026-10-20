/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Cofibered.Pushforward

/-!
# Pushforwards in categories cofibered in groupoids

The strongly cocartesian lift and cleavage API is owned by
`ReasLib.CategoryTheory.Cofibered.Pushforward`.
-/

@[expose] public section

namespace CategoryTheory

universe u v w vS
variable {C : Type u} [Category.{v} C] {F : Type w} [Category.{vS} F]
variable (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
variable {x : F} {V : C} (f : p.obj x ⟶ V)

#check (CategoryTheory.Functor.StronglyCocartesianLift p f : Type max w vS)
#check (CategoryTheory.Functor.pushforward_unique :
  {F : Type w} → [Category.{vS} F] → {q : F ⥤ C} → [Functor.IsFibered.InGroupoids q.op] →
    {U V : C} → {x y y' : F} → (f : U ⟶ V) →
      (φ : x ⟶ y) → (ψ : x ⟶ y') → [q.IsHomLift f φ] → [q.IsHomLift f ψ] →
        ∃! τ : y ⟶ y', q.IsHomLift (𝟙 V) τ ∧ φ ≫ τ = ψ ∧ IsIso τ)
#check (CategoryTheory.Functor.cleavageOp p : p.op.Cleavage)

end CategoryTheory
