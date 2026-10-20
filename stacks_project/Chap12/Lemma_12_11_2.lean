/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.AbelianK0

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ₑ B)

/- Lemma 12.11.2 [02MV]: an exact functor induces an additive homomorphism on Grothendieck
groups by sending `[X]` to `[F(X)]`. -/
@[stacks 02MV]
#check (AbelianK0.map F : AbelianK0 A →+ AbelianK0 B)

variable (X : A)

/- The induced homomorphism has the expected value on every object generator. -/
#check (AbelianK0.map_of F X : AbelianK0.map F K₀[X] = K₀[F.obj.obj X])

end CategoryTheory.AbelianK0
