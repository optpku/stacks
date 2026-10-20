/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Integral finite approximation of algebraic spaces

An integral morphism of algebraic spaces over a scheme `S`, with quasi-compact
quasi-separated target, may be realized as a directed inverse limit of finite
morphisms of finite presentation into that target.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of finite morphisms of finite presentation into a
fixed target, together with a limit identification of a given integral morphism
with the cone vertex over the target. -/
structure IntegralFiniteApproximation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] where
  /-- The directed index type of the approximating inverse system. -/
  I : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderI : Preorder I]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating algebraic spaces over `S`. -/
  D : OrderDual I ⥤ AlgebraicSpace S
  /-- The structure morphisms of the approximating stages over `Y`. -/
  σ : D ⟶ (Functor.const (OrderDual I)).obj Y
  /-- A cone from the approximating inverse system. -/
  c : Cone D
  /-- The cone is a limit cone. -/
  isLimit : IsLimit c
  /-- The identification of `X` with the vertex of the limit cone. -/
  iso : X ≅ c.pt
  /-- After identifying `X` with the cone vertex, the cone legs recover `f` over `Y`. -/
  over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f
  /-- Every approximating stage is finite over `Y`. -/
  stageFinite : ∀ i, IsFinite (σ.app i)
  /-- Every approximating stage is of finite presentation over `Y`. -/
  stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)

namespace IntegralFiniteApproximation

/-- Package a directed inverse system of finite morphisms of finite presentation
into `Y`, together with a limit identification recovering `f`. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
    (stageFinite : ∀ i, IsFinite (σ.app i))
    (stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)) :
    IntegralFiniteApproximation f where
  I := I
  D := D
  σ := σ
  c := c
  isLimit := isLimit
  iso := iso
  over_lim := over_lim
  stageFinite := stageFinite
  stageFinitePresentation := stageFinitePresentation

/-- The algebraic space at a given stage of an integral finite approximation. -/
def stage {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] (A : IntegralFiniteApproximation f) (i : A.I) :
    AlgebraicSpace S :=
  @Functor.obj _ (@Preorder.smallCategory _ (@OrderDual.instPreorder _ A.preorderI))
    _ _ A.D i

/-- The structure morphism from a stage of an integral finite approximation to its target. -/
def stageHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] (A : IntegralFiniteApproximation f) (i : A.I) :
    A.stage i ⟶ Y :=
  @NatTrans.app _ (@Preorder.smallCategory _ (@OrderDual.instPreorder _ A.preorderI))
    _ _ _ _ A.σ i

/-- The projection from the source to a stage through the limit identification. -/
def toStage {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] (A : IntegralFiniteApproximation f) (i : A.I) :
    X ⟶ A.stage i :=
  A.iso.hom ≫
    @NatTrans.app _ (@Preorder.smallCategory _ (@OrderDual.instPreorder _ A.preorderI))
      _ _ _ _
      (@Cone.π _ (@Preorder.smallCategory _ (@OrderDual.instPreorder _ A.preorderI))
        _ _ A.D A.c) i

/-- An integral finite approximation recovers `f` over `Y`, with finite
morphisms of finite presentation as stages. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] (A : IntegralFiniteApproximation f) :
    (∀ i : A.I, A.toStage i ≫ A.stageHom i = f) ∧
      (∀ i : A.I, IsFinite (A.stageHom i)) ∧
      ∀ i : A.I, FinitePresentation (A.stageHom i) :=
  sorry

end IntegralFiniteApproximation

/-- An integral morphism of algebraic spaces over a scheme, with quasi-compact
quasi-separated target, admits a directed inverse system of finite morphisms of
finite presentation into the target whose limit is identified with the source. -/
theorem exists_integralFiniteApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (IntegralFiniteApproximation f) :=
  sorry

/-- For an integral morphism with quasi-compact, quasi-separated target, an
integral finite approximation exists if and only if there is a directed inverse
system of finite morphisms of finite presentation over the target with a limit
identification of the source recovering the morphism. -/
theorem exists_integralFiniteApproximation_nonempty_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (IntegralFiniteApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace S)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) (c : Cone D)
        (_ : IsLimit c) (iso : X ≅ c.pt)
        (_ : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
        (_ : ∀ i, IsFinite (σ.app i)),
        ∀ i, FinitePresentation (σ.app i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
