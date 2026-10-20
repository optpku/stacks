/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat morphisms in finite-type approximation systems of algebraic spaces

Flat morphisms of finite presentation between the limits of finite-type
approximation systems of algebraic spaces descend on a sufficiently late
common tail, where their stage squares are cartesian.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace InverseSystemMorphismOverBase

/-- The flatness and cartesian base-change conditions at and beyond a fixed stage of a
morphism between inverse systems of algebraic spaces. -/
structure FlatBaseChangeAt
    {I : Type u} [Preorder I] {i₀ i₃ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃) (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) : Prop where
  /-- Every morphism at a stage beyond the fixed stage is flat. -/
  flat_stage : ∀ (i : I) (hi₃i : i₃ ≤ i),
    Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
  /-- Every later stage is obtained from the fixed stage by the corresponding cartesian square. -/
  stage_isPullback : ∀ (i : I) (hi₃i : i₃ ≤ i),
    IsPullback
      (Xsys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
      (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (Ysys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
  /-- The limit square over the fixed stage is cartesian. -/
  limit_isPullback :
    IsPullback
      (xCone.π.app (tailObject i₃ hi₀i₃))
      f
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (yCone.π.app (tailObject i₃ hi₀i₃))

namespace FlatBaseChangeAt

/-- Assemble the flatness and cartesian base-change conditions at a fixed stage. -/
def ofConditions
    {I : Type u} [Preorder I] {i₀ i₃ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃) (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt)
    (flat_stage : ∀ (i : I) (hi₃i : i₃ ≤ i),
      Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))))
    (stage_isPullback : ∀ (i : I) (hi₃i : i₃ ≤ i),
      IsPullback
        (Xsys.map (Over.homMk (homOfLE hi₃i) :
          tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
        (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (Ysys.map (Over.homMk (homOfLE hi₃i) :
          tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃)))
    (limit_isPullback :
      IsPullback
        (xCone.π.app (tailObject i₃ hi₀i₃))
        f
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (yCone.π.app (tailObject i₃ hi₀i₃))) :
    FlatBaseChangeAt hi₀i₃ xCone yCone φ f where
  flat_stage := flat_stage
  stage_isPullback := stage_isPullback
  limit_isPullback := limit_isPullback

end FlatBaseChangeAt

/-- The fixed-stage flat base-change certificate is equivalent to its three defining
conditions. -/
theorem flatBaseChangeAt_iff
    {I : Type u} [Preorder I] {i₀ i₃ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃) (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) :
    FlatBaseChangeAt hi₀i₃ xCone yCone φ f ↔
      (∀ (i : I) (hi₃i : i₃ ≤ i),
        Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))) ∧
      (∀ (i : I) (hi₃i : i₃ ≤ i),
        IsPullback
          (Xsys.map (Over.homMk (homOfLE hi₃i) :
            tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
          (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
          (φ.hom.app (tailObject i₃ hi₀i₃))
          (Ysys.map (Over.homMk (homOfLE hi₃i) :
            tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))) ∧
      IsPullback
        (xCone.π.app (tailObject i₃ hi₀i₃))
        f
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (yCone.π.app (tailObject i₃ hi₀i₃)) := sorry

end InverseSystemMorphismOverBase

namespace FiniteTypeApproximationLimitSystem

/-- A flat morphism of finite presentation between the limits of finite-type
approximation systems of algebraic spaces is flat on a sufficiently late tail, and
both its later-stage squares and its limit square over the chosen stage are
cartesian. -/
@[stacks 0CPC]
theorem exists_flatBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₀ : I}
    {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₀ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₀ Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys Xapprox.toBase Yapprox.toBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hf_limit : φ.IsLimitMorphism xCone yCone f)
    (hflat : Flat f) (hfp : FinitePresentation f) :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃),
      φ.FlatBaseChangeAt hi₀i₃ xCone yCone f := sorry

end FiniteTypeApproximationLimitSystem

end AlgebraicGeometry.AlgebraicSpace
