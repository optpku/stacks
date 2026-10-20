/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Pushforwards in categories cofibered in groupoids

A pushforward of `x` along `f` is a lift of `f` through `p`. Under cofiberedness it is strongly
cocartesian and unique up to a unique vertical isomorphism. A choice of pushforwards is a
cleavage of `p.op`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

open Functor Fiber

namespace Functor

/-- A chosen strongly cocartesian lift of `f : p.obj x ⟶ V` with domain `x`.
Its target automatically lies over `V`, as witnessed by the inherited `IsHomLift`. -/
abbrev StronglyCocartesianLift (p : F ⥤ C) {x : F} {V : C} (f : p.obj x ⟶ V) :=
  {lift : Under x // p.IsStronglyCocartesian f lift.hom}

namespace StronglyCocartesianLift

variable {p : F ⥤ C} {x : F} {V : C} {f : p.obj x ⟶ V}

/-- The target of the selected strongly cocartesian arrow. -/
abbrev target (lift : StronglyCocartesianLift p f) : F :=
  lift.val.right

/-- The selected strongly cocartesian arrow with domain `x`. -/
abbrev hom (lift : StronglyCocartesianLift p f) : x ⟶ lift.target :=
  lift.val.hom

/-- The selected arrow satisfies the strongly cocartesian predicate over `f`. -/
abbrev isStronglyCocartesian (lift : StronglyCocartesianLift p f) :
    p.IsStronglyCocartesian f lift.hom := lift.property

/-- Construct a selected strongly cocartesian lift from its target, arrow, and property. -/
def mk (target : F) (hom : x ⟶ target) (isStronglyCocartesian : p.IsStronglyCocartesian f hom) :
    StronglyCocartesianLift p f :=
  ⟨Under.mk hom, isStronglyCocartesian⟩

/-- The chosen arrow of a strongly cocartesian lift lies over the displayed base arrow. -/
theorem isHomLift (l : StronglyCocartesianLift p f) : p.IsHomLift f l.hom := sorry

/-- The target of a strongly cocartesian lift lies over the codomain of its base arrow. -/
@[simp]
theorem targetObj (l : StronglyCocartesianLift p f) : p.obj l.target = V := sorry

/-- Convert a strongly cartesian lift of `p.op` along `f.op` into a strongly cocartesian lift of
`p` along `f`. -/
def ofOp (l : p.op.StronglyCartesianLift (f.op)) :
    StronglyCocartesianLift p f :=
  mk l.source.unop l.hom.unop sorry

/-- The target of `ofOp l` is the unopposite of the cartesian source. -/
@[simp]
theorem ofOp_target (l : p.op.StronglyCartesianLift (f.op)) :
    (ofOp l).target = l.source.unop := sorry

/-- The arrow of `ofOp l` is the unopposite of the cartesian arrow. -/
@[simp]
theorem ofOp_hom (l : p.op.StronglyCartesianLift (f.op)) :
    (ofOp l).hom = l.hom.unop := sorry

/-- A cleavage of `p.op` supplies a strongly cocartesian pushforward of `x` along `f`. -/
noncomputable def ofCleavage (χ : p.op.Cleavage) (f : p.obj x ⟶ V) :
    StronglyCocartesianLift p f :=
  ofOp (χ.lift f.op)

/-- The pushforward selected by a cleavage is strongly cocartesian. -/
theorem ofCleavage_isStronglyCocartesian (χ : p.op.Cleavage) (f : p.obj x ⟶ V) :
    p.IsStronglyCocartesian f (ofCleavage χ f).hom := sorry

/-- A selected lift is strongly cocartesian over its displayed arrow and its target lies over
the codomain of that arrow. -/
theorem spec (lift : StronglyCocartesianLift p f) :
    p.IsStronglyCocartesian f lift.hom ∧ p.obj lift.target = V := sorry

end StronglyCocartesianLift

/-- The arrow of a supplied strongly cocartesian lift is strongly cocartesian. -/
instance instIsStronglyCocartesian_lift (p : F ⥤ C) {x : F} {V : C}
    {f : p.obj x ⟶ V} (l : StronglyCocartesianLift p f) :
    p.IsStronglyCocartesian f l.hom :=
  l.isStronglyCocartesian

/-- A functor cofibered in groupoids admits a cleavage of its opposite. This packages the axiom
of choice used to select pushforwards, via the existing cleavage constructor. -/
noncomputable def cleavageOp (p : F ⥤ C) [IsFibered.InGroupoids p.op] : p.op.Cleavage :=
  Cleavage.ofIsFibered p.op

/-- A functor cofibered in groupoids admits some choice of pushforwards. -/
theorem nonempty_cleavage_op (p : F ⥤ C) [IsFibered.InGroupoids p.op] :
    Nonempty p.op.Cleavage := sorry

/-- A pushforward of `x` along `f` is a morphism of `F` lying over `f`. Any two such lifts
through a cofibered-in-groupoids projection differ by a unique vertical isomorphism. -/
theorem pushforward_unique
    {p : F ⥤ C} [IsFibered.InGroupoids p.op]
    {U V : C} {x y y' : F} (f : U ⟶ V)
    (φ : x ⟶ y) (ψ : x ⟶ y')
    [p.IsHomLift f φ] [p.IsHomLift f ψ] :
    ∃! τ : y ⟶ y', p.IsHomLift (𝟙 V) τ ∧ φ ≫ τ = ψ ∧ IsIso τ := sorry

/-- Two chosen strongly cocartesian lifts of the same base arrow differ by a unique vertical
isomorphism. -/
theorem StronglyCocartesianLift.unique
    {p : F ⥤ C} [IsFibered.InGroupoids p.op]
    {x : F} {V : C} {f : p.obj x ⟶ V}
    (l₁ l₂ : StronglyCocartesianLift p f) :
    ∃! τ : l₁.target ⟶ l₂.target,
      p.IsHomLift (𝟙 V) τ ∧ l₁.hom ≫ τ = l₂.hom ∧ IsIso τ := sorry

end Functor

end CategoryTheory
