/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap70.Proposition_70_8_1_Approximation

/-!
# Relative Noetherian approximation of morphisms of algebraic spaces

A morphism of quasi-compact quasi-separated algebraic spaces over `Spec ℤ` may
be realized as a directed inverse limit of morphisms of quasi-separated
algebraic spaces of finite type over `ℤ`, with affine transition morphisms on
both the source and the target systems.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of morphisms of quasi-separated finite-type
algebraic spaces over `ℤ`, with affine transitions, together with a limit
identification of a given morphism with the induced map of cone vertices. -/
structure RelativeNoetherianApproximation {X Y : AlgebraicSpace specULiftInt}
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
  Xsys : OrderDual I ⥤ AlgebraicSpace specULiftInt
  /-- The inverse system of approximating target algebraic spaces over `Spec ℤ`. -/
  Ysys : OrderDual I ⥤ AlgebraicSpace specULiftInt
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
  /-- Every approximating source stage is quasi-separated. -/
  XQuasiSeparated :
    ∀ i : I, IsQuasiSeparated (Xsys.obj (OrderDual.toDual i))
  /-- Every approximating target stage is quasi-separated. -/
  YQuasiSeparated :
    ∀ i : I, IsQuasiSeparated (Ysys.obj (OrderDual.toDual i))
  /-- Every approximating source stage is of finite type over `Spec ℤ`. -/
  XFiniteType :
    ∀ i : I, FiniteType (toBase (Xsys.obj (OrderDual.toDual i)))
  /-- Every approximating target stage is of finite type over `Spec ℤ`. -/
  YFiniteType :
    ∀ i : I, FiniteType (toBase (Ysys.obj (OrderDual.toDual i)))


namespace RelativeNoetherianApproximation

/-- Package a directed inverse system of morphisms of quasi-separated finite-type
algebraic spaces over `ℤ`, with affine transitions and a limit identification,
as a relative Noetherian approximation of `f`. -/
def of {X Y : AlgebraicSpace specULiftInt} (f : X ⟶ Y)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Xsys Ysys : OrderDual I ⥤ AlgebraicSpace specULiftInt) (φ : Xsys ⟶ Ysys)
    (cX : Cone Xsys) (cY : Cone Ysys) (isLimitX : IsLimit cX) (isLimitY : IsLimit cY)
    (isoX : X ≅ cX.pt) (isoY : Y ≅ cY.pt)
    (stage_comm :
      ∀ i, isoX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ isoY.hom ≫ cY.π.app i)
    (XtransitionAffine :
      ∀ {i i' : I} (h : i ≤ i'), Affine (Xsys.map (homOfLE h)))
    (YtransitionAffine :
      ∀ {i i' : I} (h : i ≤ i'), Affine (Ysys.map (homOfLE h)))
    (XQuasiSeparated :
      ∀ i : I, IsQuasiSeparated (Xsys.obj (OrderDual.toDual i)))
    (YQuasiSeparated :
      ∀ i : I, IsQuasiSeparated (Ysys.obj (OrderDual.toDual i)))
    (XFiniteType :
      ∀ i : I, FiniteType (toBase (Xsys.obj (OrderDual.toDual i))))
    (YFiniteType :
      ∀ i : I, FiniteType (toBase (Ysys.obj (OrderDual.toDual i)))) :
    RelativeNoetherianApproximation f where
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
  XQuasiSeparated := XQuasiSeparated
  YQuasiSeparated := YQuasiSeparated
  XFiniteType := XFiniteType
  YFiniteType := YFiniteType

/-- A relative Noetherian approximation recovers `f` as the limit of the stage
morphisms, with affine transitions and quasi-separated finite-type stages over
`ℤ`. -/
-- Local instance justification (defeq pin): the functor and `homOfLE` data of
-- `A` are typed using the stored `A.preorderI`.
theorem spec {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) :
    letI := A.preorderI
    (∀ i, A.isoX.hom ≫ A.cX.π.app i ≫ A.φ.app i =
      f ≫ A.isoY.hom ≫ A.cY.π.app i) ∧
    (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.Xsys.map (homOfLE h))) ∧
    (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.Ysys.map (homOfLE h))) ∧
    (∀ i, IsQuasiSeparated (A.Xsys.obj (OrderDual.toDual i))) ∧
    (∀ i, IsQuasiSeparated (A.Ysys.obj (OrderDual.toDual i))) ∧
    (∀ i, FiniteType (toBase (A.Xsys.obj (OrderDual.toDual i)))) ∧
    ∀ i, FiniteType (toBase (A.Ysys.obj (OrderDual.toDual i))) :=
  sorry

/-- The morphism of cone vertices induced by the approximating system `φ`. -/
-- Local instance justification (defeq pin): `A.Xsys` and `A.Ysys` are functors
-- on `OrderDual A.I` for the stored `A.preorderI`, which must match the
-- `Category` instance used by `Cone.postcompose`.
def limMap {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) :
    letI := A.preorderI
    A.cX.pt ⟶ A.cY.pt :=
  letI := A.preorderI
  A.isLimitY.lift ((Cone.postcompose A.φ).obj A.cX)

/-- The induced limit morphism commutes with the cone legs and the stage maps. -/
-- Local instance justification (defeq pin): cone legs of `A.cX`/`A.cY` are
-- typed using the stored `A.preorderI` rather than a fresh `Preorder A.I`.
theorem limMap_π {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) (i : OrderDual A.I) :
    letI := A.preorderI
    A.limMap ≫ A.cY.π.app i = A.cX.π.app i ≫ A.φ.app i :=
  sorry

/-- After identifying the cone vertices with `X` and `Y`, the induced limit
morphism recovers `f`. -/
-- Local instance justification (defeq pin): `A.limMap` is typed using the
-- stored `A.preorderI` on the approximating index.
theorem limMap_comm {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) :
    letI := A.preorderI
    A.isoX.hom ≫ A.limMap = f ≫ A.isoY.hom :=
  sorry

/-- The source inverse system of a relative approximation is an absolute
Noetherian approximation of `X`. -/
def sourceApprox {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) :
    AbsoluteNoetherianApproximation X where
  I := A.I
  preorderI := A.preorderI
  nonemptyI := A.nonemptyI
  directedI := A.directedI
  D := A.Xsys
  c := A.cX
  isLimit := A.isLimitX
  iso := A.isoX
  transitionAffine := A.XtransitionAffine
  stageQuasiSeparated := A.XQuasiSeparated
  stageFiniteType := A.XFiniteType

/-- The target inverse system of a relative approximation is an absolute
Noetherian approximation of `Y`. -/
def targetApprox {X Y : AlgebraicSpace specULiftInt} {f : X ⟶ Y}
    (A : RelativeNoetherianApproximation f) :
    AbsoluteNoetherianApproximation Y where
  I := A.I
  preorderI := A.preorderI
  nonemptyI := A.nonemptyI
  directedI := A.directedI
  D := A.Ysys
  c := A.cY
  isLimit := A.isLimitY
  iso := A.isoY
  transitionAffine := A.YtransitionAffine
  stageQuasiSeparated := A.YQuasiSeparated
  stageFiniteType := A.YFiniteType

end RelativeNoetherianApproximation

/-- A morphism of quasi-compact quasi-separated algebraic spaces over `Spec ℤ`
admits a directed inverse system of morphisms of quasi-separated finite-type
algebraic spaces over `ℤ`, with affine transitions, whose limit is identified
with it. -/
theorem exists_relativeNoetherianApproximation
    {X Y : AlgebraicSpace specULiftInt} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact Y] [IsQuasiSeparated Y] :
    Nonempty (RelativeNoetherianApproximation f) :=
  sorry

/-- Relative Noetherian approximation of a morphism of qcqs algebraic spaces
over `Spec ℤ` is equivalent to the existence of a common directed inverse system
of morphisms with affine transitions, quasi-separated finite-type stages over
`ℤ`, and a limit identification of `f`. -/
theorem exists_relativeNoetherianApproximation_nonempty_iff
    {X Y : AlgebraicSpace specULiftInt} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact Y] [IsQuasiSeparated Y] :
    Nonempty (RelativeNoetherianApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (Xsys Ysys : OrderDual I ⥤ AlgebraicSpace specULiftInt) (φ : Xsys ⟶ Ysys)
        (cX : Cone Xsys) (cY : Cone Ysys) (_ : IsLimit cX) (_ : IsLimit cY)
        (isoX : X ≅ cX.pt) (isoY : Y ≅ cY.pt)
        (_ : ∀ i, isoX.hom ≫ cX.π.app i ≫ φ.app i = f ≫ isoY.hom ≫ cY.π.app i)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (Xsys.map (homOfLE h)))
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (Ysys.map (homOfLE h)))
        (_ : ∀ i, IsQuasiSeparated (Xsys.obj (OrderDual.toDual i)))
        (_ : ∀ i, IsQuasiSeparated (Ysys.obj (OrderDual.toDual i)))
        (_ : ∀ i, FiniteType (toBase (Xsys.obj (OrderDual.toDual i)))),
        ∀ i, FiniteType (toBase (Ysys.obj (OrderDual.toDual i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
