/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

/- Semantic recall hits used for this setup item:
- `CategoryTheory.IsPullback`,
- `AlgebraicGeometry.Scheme.Modules.pullback`,
- `AlgebraicGeometry.Scheme.Modules.pushforward`,
- `CategoryTheory.Functor.rightDerived`. -/

namespace AlgebraicGeometry.Scheme

variable {X X' S S' : Scheme.{u}}
variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (ℱ : X.Modules)

/- 30.5.0.1: the displayed geometric square is cartesian. -/
@[stacks 02KF] #check (CategoryTheory.IsPullback g' f' f g : Prop)

#check (AlgebraicGeometry.Scheme.Modules.pullback :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Y.Modules ⥤ X.Modules)
#check (AlgebraicGeometry.Scheme.Modules.pushforward :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)
#check (CategoryTheory.Functor.rightDerived :
  ∀ {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (i : ℕ), C ⥤ D)

#check ((Scheme.Modules.pullback g').obj ℱ : X'.Modules)

section

variable [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
variable (i : ℕ)

#check (((Scheme.Modules.pushforward f').rightDerived i).obj
  ((Scheme.Modules.pullback g').obj ℱ) : S'.Modules)
#check (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ : S.Modules)

end

end AlgebraicGeometry.Scheme
