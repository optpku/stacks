/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Schemes over an algebraic space

Scheme-valued points over an algebraic space are fibers of its functor of points.
The category of schemes over that space carries the induced fppf topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemesOver

/-- The Yoneda identification of an `Over B` morphism out of a scheme over `B` with a
scheme-valued point of the underlying algebraic space. -/
def toFunctorOfPoints {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (f : Over.mk σ ⟶ U) :
    U.left.functorOfPoints.obj (op T) :=
  yonedaEquiv (f.left : yoneda.obj T ⟶ U.left.functorOfPoints)

/-- `toFunctorOfPoints` is `yonedaEquiv` of the underlying algebraic-space morphism. -/
theorem toFunctorOfPoints_eq {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (f : Over.mk σ ⟶ U) :
    toFunctorOfPoints f =
      yonedaEquiv (f.left : yoneda.obj T ⟶ U.left.functorOfPoints) :=
  rfl

/-- The fiber of scheme-valued points of `U` over a structure morphism `σ`. -/
def schemePointFiber {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B)
    {T : Over S} (σ : ofOver T ⟶ B) : Type u :=
  { x : U.left.functorOfPoints.obj (op T) //
      U.hom.app (op T) x = yonedaEquiv σ }

/-- A point of `schemePointFiber` maps to `σ` in `B`. -/
theorem mem_schemePointFiber {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (x : schemePointFiber U σ) :
    U.hom.app (op T) x.val = yonedaEquiv σ :=
  x.property

/-- The Yoneda identification of an `Over B` morphism lands in the fiber over `σ`. -/
theorem toFunctorOfPoints_hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (f : Over.mk σ ⟶ U) :
    U.hom.app (op T) (toFunctorOfPoints f) = yonedaEquiv σ :=
  ((yonedaEquiv_comp
      (f.left : yoneda.obj T ⟶ U.left.functorOfPoints) U.hom).symm).trans
    (congrArg yonedaEquiv f.w)

/-- The fiber representative of an `Over B` morphism. -/
def toFunctorOfPointsFiber {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (f : Over.mk σ ⟶ U) :
    schemePointFiber U σ :=
  ⟨toFunctorOfPoints f, toFunctorOfPoints_hom_eq f⟩

/-- `toFunctorOfPointsFiber` forgets to `toFunctorOfPoints`. -/
theorem toFunctorOfPointsFiber_val {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} {T : Over S} {σ : ofOver T ⟶ B} (f : Over.mk σ ⟶ U) :
    (toFunctorOfPointsFiber f).val = toFunctorOfPoints f :=
  rfl

/-- The inverse Yoneda identification of a fiber point with an `Over B` morphism. -/
def ofFunctorOfPointsFiber {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {T : Over S} {σ : ofOver T ⟶ B} (x : schemePointFiber U σ) :
    Over.mk σ ⟶ U :=
  Over.homMk (yonedaEquiv.symm x.val) sorry

/-- `ofFunctorOfPointsFiber` is `yonedaEquiv.symm` of the underlying point. -/
theorem ofFunctorOfPointsFiber_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} {T : Over S} {σ : ofOver T ⟶ B} (x : schemePointFiber U σ) :
    (ofFunctorOfPointsFiber x).left = yonedaEquiv.symm x.val :=
  rfl

/-- Restriction of schemes over `S` preserves fibers over `B`. -/
theorem schemePointFiber_map_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} {T T' : Over S} (f : T' ⟶ T) {σ : ofOver T ⟶ B}
    (x : schemePointFiber U σ) :
    U.hom.app (op T') (U.left.functorOfPoints.map f.op x.val) =
      yonedaEquiv ((ofOverFunctor S).map f ≫ σ) :=
  sorry

/-- Restriction of a fiber point along a morphism of schemes over `B`. -/
theorem schemePointFiber_comap_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} {σ τ : CostructuredArrow (ofOverFunctor S) B} (f : τ ⟶ σ)
    (x : schemePointFiber U σ.hom) :
    U.hom.app (op τ.left) (U.left.functorOfPoints.map f.left.op x.val) =
      yonedaEquiv τ.hom :=
  sorry

/-- Restriction of fiber points along a morphism of schemes over `B`. -/
def schemePointFiber_comap {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {σ τ : CostructuredArrow (ofOverFunctor S) B} (f : τ ⟶ σ)
    (x : schemePointFiber U σ.hom) :
    schemePointFiber U τ.hom :=
  ⟨U.left.functorOfPoints.map f.left.op x.val, schemePointFiber_comap_hom f x⟩

/-- The topology on schemes over an algebraic space induced from the fppf topology
on algebraic spaces over it. -/
abbrev fppfTopology {S : Scheme.{u}} (B : AlgebraicSpace S) :
    GrothendieckTopology (CostructuredArrow (ofOverFunctor S) B) :=
  (CostructuredArrow.toOver (ofOverFunctor S) B).inducedTopology
    ((fppfPrecoverage S).toGrothendieck.over B)

/-- The topology on schemes over an algebraic space is induced by the canonical
functor to algebraic spaces over that base. -/
theorem fppfTopology_eq_induced {S : Scheme.{u}} (B : AlgebraicSpace S) :
    fppfTopology B =
      (CostructuredArrow.toOver (ofOverFunctor S) B).inducedTopology
        ((fppfPrecoverage S).toGrothendieck.over B) :=
  rfl

/-- The induced fppf topology on schemes over an algebraic space is generated by
fppf covering families of their underlying schemes. -/
theorem fppfTopology_eq_comap {S : Scheme.{u}} (B : AlgebraicSpace S) :
    fppfTopology B =
      (Scheme.fppfPrecoverage.comap
        (CostructuredArrow.proj (ofOverFunctor S) B ⋙ Over.forget S)).toGrothendieck :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SchemesOver
