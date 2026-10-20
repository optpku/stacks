/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Proper Noetherian approximation of morphisms of algebraic spaces

A proper morphism of algebraic spaces over `Spec ℤ`, with quasi-compact
quasi-separated target, may be realized as a directed inverse limit of proper
morphisms of finite presentation, with affine transitions on both systems and
with each target stage of finite presentation over `ℤ`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of proper morphisms of finite presentation over
`ℤ`, with affine transitions and target stages of finite presentation over `ℤ`,
together with a limit identification of a given morphism with the
induced map of cone vertices. -/
structure ProperNoetherianApproximation {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : X ⟶ Y) where
  /-- The directed index type of the approximating inverse systems. -/
  I : Type u
  /-- The preorder on the common index type of the approximating inverse systems. -/
  [preorderI : Preorder I]
  /-- The approximating inverse systems have at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse systems admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating source algebraic spaces over `Spec ℤ`. -/
  Xsys : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))
  /-- The inverse system of approximating target algebraic spaces over `Spec ℤ`. -/
  Ysys : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))
  /-- The morphism of inverse systems approximating `f`. -/
  φ : Xsys ⟶ Ysys
  /-- A cone from the approximating source inverse system. -/
  cX : Cone Xsys
  /-- A cone from the approximating target inverse system. -/
  cY : Cone Ysys
  /-- The source cone is a limit cone. -/
  isLimitX : IsLimit cX
  /-- The target cone is a limit cone. -/
  isLimitY : IsLimit cY
  /-- The identification of `X` with the vertex of the source limit cone. -/
  isoX : X ≅ cX.pt
  /-- The identification of `Y` with the vertex of the target limit cone. -/
  isoY : Y ≅ cY.pt
  /-- Stagewise, the identifications intertwine `f` with the components of `φ`. -/
  stage_comm :
    ∀ i, isoX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ isoY.hom ≫ cY.π.app i
  /-- Every source transition morphism in the inverse system is affine. -/
  XtransitionAffine :
    ∀ {i i' : I} (h : i ≤ i'), Affine (Xsys.map (homOfLE h))
  /-- Every target transition morphism in the inverse system is affine. -/
  YtransitionAffine :
    ∀ {i i' : I} (h : i ≤ i'), Affine (Ysys.map (homOfLE h))
  /-- Every approximating stage morphism is proper. -/
  stageProper : ∀ i, Proper (φ.app i)
  /-- Every approximating stage morphism is of finite presentation. -/
  stageFinitePresentation : ∀ i, FinitePresentation (φ.app i)
  /-- Every approximating target stage is of finite presentation over `Spec ℤ`. -/
  YFinitePresentation :
    ∀ i : I, FinitePresentation (SchemeRealization.toBase (Ysys.obj (OrderDual.toDual i)))

namespace ProperNoetherianApproximation

/-- A directed inverse system of proper morphisms of finite presentation over
`ℤ`, with affine transitions, target stages of finite presentation over `ℤ`,
and a limit identification of `f`, determines a proper Noetherian approximation
of `f`. -/
def of {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Xsys Ysys : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (φ : Xsys ⟶ Ysys)
    (cX : Cone Xsys) (cY : Cone Ysys) (isLimitX : IsLimit cX) (isLimitY : IsLimit cY)
    (isoX : X ≅ cX.pt) (isoY : Y ≅ cY.pt)
    (stage_comm :
      ∀ i, isoX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ isoY.hom ≫ cY.π.app i)
    (XtransitionAffine :
      ∀ {i i' : I} (h : i ≤ i'), Affine (Xsys.map (homOfLE h)))
    (YtransitionAffine :
      ∀ {i i' : I} (h : i ≤ i'), Affine (Ysys.map (homOfLE h)))
    (stageProper : ∀ i, Proper (φ.app i))
    (stageFinitePresentation : ∀ i, FinitePresentation (φ.app i))
    (YFinitePresentation :
      ∀ i : I, FinitePresentation (SchemeRealization.toBase (Ysys.obj (OrderDual.toDual i)))) :
    ProperNoetherianApproximation f where
  I := I
  Xsys := Xsys
  Ysys := Ysys
  φ := φ
  cX := cX
  cY := cY
  isLimitX := isLimitX
  isLimitY := isLimitY
  isoX := isoX
  isoY := isoY
  stage_comm := stage_comm
  XtransitionAffine := XtransitionAffine
  YtransitionAffine := YtransitionAffine
  stageProper := stageProper
  stageFinitePresentation := stageFinitePresentation
  YFinitePresentation := YFinitePresentation

/-- A proper Noetherian approximation recovers `f` as the limit of the stage
morphisms, with affine transitions, proper finite-presentation stages, and
target stages of finite presentation over `ℤ`. -/
theorem spec {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} {f : X ⟶ Y}
    (A : ProperNoetherianApproximation f) :
    -- Local instance justification (defeq pin): stored `A.preorderI` types `homOfLE` and functor data.
    letI := A.preorderI
    (∀ i, A.isoX.hom ≫ A.cX.π.app i ≫ A.φ.app i =
      f ≫ A.isoY.hom ≫ A.cY.π.app i) ∧
    (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.Xsys.map (homOfLE h))) ∧
    (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.Ysys.map (homOfLE h))) ∧
    (∀ i, Proper (A.φ.app i)) ∧
    (∀ i, FinitePresentation (A.φ.app i)) ∧
    ∀ i, FinitePresentation (SchemeRealization.toBase (A.Ysys.obj (OrderDual.toDual i))) :=
  sorry

/-- The morphism of cone vertices induced by the approximating system `φ`. -/
def limMap {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} {f : X ⟶ Y}
    (A : ProperNoetherianApproximation f) :
    -- Local instance justification (defeq pin): stored `A.preorderI` is the `Category` used by `Cone.postcompose`.
    letI := A.preorderI
    A.cX.pt ⟶ A.cY.pt :=
  -- Local instance justification (defeq pin): stored `A.preorderI` is the `Category` used by `Cone.postcompose`.
  letI := A.preorderI
  A.isLimitY.lift ((Cone.postcompose A.φ).obj A.cX)

/-- The induced limit morphism commutes with the cone legs and the stage maps. -/
theorem limMap_π {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} {f : X ⟶ Y}
    (A : ProperNoetherianApproximation f) (i : OrderDual A.I) :
    -- Local instance justification (defeq pin): cone legs of `A` are typed using stored `A.preorderI`.
    letI := A.preorderI
    A.limMap ≫ A.cY.π.app i = A.cX.π.app i ≫ A.φ.app i :=
  sorry

/-- After identifying the cone vertices with `X` and `Y`, the induced limit
morphism recovers `f`. -/
theorem limMap_comm {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} {f : X ⟶ Y}
    (A : ProperNoetherianApproximation f) :
    -- Local instance justification (defeq pin): `A.limMap` is typed using stored `A.preorderI`.
    letI := A.preorderI
    A.isoX.hom ≫ A.limMap = f ≫ A.isoY.hom :=
  sorry

end ProperNoetherianApproximation

/-- A proper morphism of algebraic spaces over `Spec ℤ`, with quasi-compact
quasi-separated target, admits a directed inverse system of proper morphisms of
finite presentation, with affine transitions on both systems and with each
target stage of finite presentation over `ℤ`, whose limit is identified with
it. -/
theorem exists_properNoetherianApproximation
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
    [Proper f] [IsQuasiCompact Y] [IsQuasiSeparated Y] :
    Nonempty (ProperNoetherianApproximation f) :=
  sorry

/-- A proper Noetherian approximation of a morphism of algebraic spaces over
`Spec ℤ` exists if and only if there exists a common
directed inverse system of proper finite-presentation morphisms with affine
transitions, target stages of finite presentation over `ℤ`, and a limit
identification of `f`. -/
theorem exists_properNoetherianApproximation_nonempty_iff
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : X ⟶ Y) :
    Nonempty (ProperNoetherianApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (Xsys Ysys : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (φ : Xsys ⟶ Ysys)
        (cX : Cone Xsys) (cY : Cone Ysys) (_ : IsLimit cX) (_ : IsLimit cY)
        (isoX : X ≅ cX.pt) (isoY : Y ≅ cY.pt)
        (_ : ∀ i, isoX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ isoY.hom ≫ cY.π.app i)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (Xsys.map (homOfLE h)))
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (Ysys.map (homOfLE h)))
        (_ : ∀ i, Proper (φ.app i))
        (_ : ∀ i, FinitePresentation (φ.app i)),
        ∀ i, FinitePresentation (SchemeRealization.toBase (Ysys.obj (OrderDual.toDual i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
