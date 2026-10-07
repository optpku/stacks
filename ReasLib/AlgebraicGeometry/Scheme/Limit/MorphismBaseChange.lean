module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A morphism between quasi-compact, quasi-separated schemes over a distinguished
stage of a directed inverse system with affine transition morphisms, together with a
specified limiting cone. -/
structure QcqsMorphismBaseChange {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (i0 : I)
    (X0 Y0 : Scheme.{u}) [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0] [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))] where
  /-- The specified limiting cone of the inverse system. -/
  limitCone : LimitCone D
  /-- The structure morphism from the source scheme to the distinguished stage. -/
  sourceMap : X0 ⟶ D.obj i0
  /-- The structure morphism from the target scheme to the distinguished stage. -/
  targetMap : Y0 ⟶ D.obj i0
  /-- The morphism over the distinguished stage. -/
  hom : X0 ⟶ Y0
  /-- The compatibility of the morphism with the two structure morphisms. -/
  hom_over : hom ≫ targetMap = sourceMap

namespace QcqsMorphismBaseChange

section Constructor

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (i0 : I) (X0 Y0 : Scheme.{u})
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

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
variable {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- The target of the base-changed morphism at a stage mapping to the distinguished stage. -/
def stageTarget (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    Scheme.{u} :=
  pullback s.targetMap (D.map (homOfLE hi0i))

/-- The source of the base-changed morphism at a stage mapping to the distinguished stage. -/
def stageSource (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    Scheme.{u} :=
  pullback s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The base change of the morphism to a stage mapping to the distinguished stage. -/
def stageHom (s : QcqsMorphismBaseChange D i0 X0 Y0) (i : I) (hi0i : i0 ≤ i) :
    s.stageSource i hi0i ⟶ s.stageTarget i hi0i :=
  pullback.snd s.hom (pullback.fst s.targetMap (D.map (homOfLE hi0i)))

/-- The target of the base-changed morphism over the vertex of the limiting cone. -/
def limitTarget (s : QcqsMorphismBaseChange D i0 X0 Y0) : Scheme.{u} :=
  pullback s.targetMap (s.limitCone.cone.π.app i0)

/-- The source of the base-changed morphism over the vertex of the limiting cone. -/
def limitSource (s : QcqsMorphismBaseChange D i0 X0 Y0) : Scheme.{u} :=
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

end BaseChange

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
