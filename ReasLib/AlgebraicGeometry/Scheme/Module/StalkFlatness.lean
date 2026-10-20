/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The stalk of a source module, regarded as a module over the target local ring via the
stalk map of a scheme morphism. -/
def targetStalkOver (F : X.Modules) (f : X ⟶ Y) (point : X) :
    ModuleCat (Y.presheaf.stalk (f point)) :=
  (ModuleCat.restrictScalars (f.stalkMap point).hom).obj
    ((SheafOfModules.stalkFunctorOfCommRing X.sheaf point).obj F)

/-- A scheme module is stalkwise flat over a target scheme if each source stalk is flat
over the corresponding target local ring. -/
def IsStalkFlatOver (F : X.Modules) (f : X ⟶ Y) : Prop :=
  ∀ point : X, Module.Flat (Y.presheaf.stalk (f point)) (targetStalkOver F f point)

/-- Stalkwise relative flatness is equivalent to flatness of every stalk module after
restriction of scalars along the target local-ring map. -/
theorem isStalkFlatOver_iff (F : X.Modules) (f : X ⟶ Y) :
    IsStalkFlatOver F f ↔
      ∀ point : X, Module.Flat (Y.presheaf.stalk (f point)) (targetStalkOver F f point) := sorry

end AlgebraicGeometry.Scheme.Modules
