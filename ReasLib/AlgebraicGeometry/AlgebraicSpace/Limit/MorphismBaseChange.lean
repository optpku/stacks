/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Morphisms over a distinguished stage of a directed affine inverse system

A morphism between quasi-compact algebraic spaces, quasi-separated relative to `S`, over a
distinguished stage of a directed inverse system with affine transition
morphisms, together with a specified limiting cone.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- A morphism between quasi-compact algebraic spaces, quasi-separated relative to `S`, over a
distinguished stage of a directed inverse system with affine transition
morphisms, together with a specified limiting cone. -/
structure QcqsMorphismBaseChange {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (i0 : I) (X0 Y0 : AlgebraicSpace S)
    [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
    [IsQuasiCompact X0] [IsQuasiSeparated X0]
    [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))] where
  /-- The specified limiting cone of the inverse system. -/
  limitCone : LimitCone D
  /-- The structure morphism from the source algebraic space to the distinguished stage. -/
  sourceMap : X0 ⟶ D.obj i0
  /-- The structure morphism from the target algebraic space to the distinguished stage. -/
  targetMap : Y0 ⟶ D.obj i0
  /-- The morphism over the distinguished stage. -/
  hom : X0 ⟶ Y0
  /-- The compatibility of the morphism with the two structure morphisms. -/
  hom_over : hom ≫ targetMap = sourceMap

namespace QcqsMorphismBaseChange

section Constructor

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (i0 : I) (X0 Y0 : AlgebraicSpace S)
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- Construct a morphism base-change setup from a limiting cone and compatible
morphisms over the distinguished stage. -/
def ofCone (c : Cone D) (hc : IsLimit c) (x0 : X0 ⟶ D.obj i0)
    (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0) :
    QcqsMorphismBaseChange D i0 X0 Y0 where
  limitCone := ⟨c, hc⟩
  sourceMap := x0
  targetMap := y0
  hom := f0
  hom_over := hf0

/-- The constructor preserves the specified limiting cone, structure morphisms,
morphism, and compatibility equation. -/
theorem ofCone_spec (c : Cone D) (hc : IsLimit c) (x0 : X0 ⟶ D.obj i0)
    (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0) :
    (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).limitCone.cone = c ∧
      (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).limitCone.isLimit = hc ∧
      (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).sourceMap = x0 ∧
      (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).targetMap = y0 ∧
      (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).hom = f0 ∧
      (ofCone D i0 X0 Y0 c hc x0 y0 f0 hf0).hom_over = hf0 := sorry

end Constructor

section BaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable {i0 : I} {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The target of the base-changed morphism at a stage mapping to the distinguished stage. -/
def stageTarget (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    AlgebraicSpace S :=
  pullback s.targetMap (D.map (homOfLE hi0i))

/-- The source of the base-changed morphism at a stage mapping to the distinguished stage. -/
def stageSource (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    AlgebraicSpace S :=
  pullback s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The base change of the morphism to a stage mapping to the distinguished stage. -/
def stageHom (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    s.stageSource i hi0i ⟶ s.stageTarget i hi0i :=
  pullback.snd s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The target of the base-changed morphism over the vertex of the limiting cone. -/
def limitTarget (s : QcqsMorphismBaseChange D i0 X0 Y0) : AlgebraicSpace S :=
  pullback s.targetMap (s.limitCone.cone.π.app i0)

/-- The source of the base-changed morphism over the vertex of the limiting cone. -/
def limitSource (s : QcqsMorphismBaseChange D i0 X0 Y0) : AlgebraicSpace S :=
  pullback s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0))

/-- The base change of the morphism to the vertex of the limiting cone. -/
def limitHom (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitSource ⟶ s.limitTarget :=
  pullback.snd s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0))

/-- The stagewise base-changed morphism is the canonical second pullback projection. -/
theorem stageHom_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I)
    (hi0i : i0 ≤ i) :
    s.stageHom i hi0i =
      pullback.snd s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i))) := sorry

/-- The limit base-changed morphism is the canonical second pullback projection. -/
theorem limitHom_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitHom =
      pullback.snd s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0)) := sorry

/-- The canonical morphism `Xᵢ ⟶ X₀` from the stagewise source pullback. -/
def stageSourceMap (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    s.stageSource i hi0i ⟶ X0 :=
  pullback.fst s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The canonical morphism `X ⟶ X₀` from the limit source pullback. -/
def limitSourceMap (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitSource ⟶ X0 :=
  pullback.fst s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0))

/-- The stagewise source map is the canonical first pullback projection. -/
theorem stageSourceMap_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I)
    (hi0i : i0 ≤ i) :
    s.stageSourceMap i hi0i =
      pullback.fst s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i))) := rfl

/-- The limit source map is the canonical first pullback projection. -/
theorem limitSourceMap_apply (s : QcqsMorphismBaseChange D i0 X0 Y0) :
    s.limitSourceMap =
      pullback.fst s.hom (pullback.fst s.targetMap (s.limitCone.cone.π.app i0)) := rfl

end BaseChange

end QcqsMorphismBaseChange

end AlgebraicGeometry.AlgebraicSpace.Limit
