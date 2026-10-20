/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Realization of schemes as algebraic spaces

Schemes over `S` embed into algebraic spaces over `S`, with structural morphisms,
fibre-product projections, and product comparisons.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry CategoryTheory MonoidalCategory
open CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-- The morphism of algebraic spaces represented by a morphism of schemes over `S`. -/
def ofOverMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) : ofOver U ⟶ ofOver V :=
  (yoneda.map f : yoneda.obj U ⟶ yoneda.obj V)

/-- The structural morphism from an algebraic space over `S` to `S` as an algebraic space. -/
def toBase {S : Scheme.{u}} (X : AlgebraicSpace S) : X ⟶ ofOver (Over.mk (𝟙 S)) where
  app T := ↾fun _ ↦ Over.homMk T.unop.hom
  naturality := sorry

/-- Every morphism from an algebraic space over `S` to `S` equals `toBase`. -/
theorem eq_toBase {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) : f = toBase X :=
  sorry

/-- The functor sending a scheme over `S` to its associated algebraic space over `S`. -/
def ofOverSlice (S : Scheme.{u}) : Over S ⥤ Over (ofOver (Over.mk (𝟙 S))) where
  obj T := Over.mk (toBase (ofOver T))
  map f := Over.homMk (ofOverMap f) (eq_toBase _)
  map_id := sorry
  map_comp := sorry

/-- The object map of `ofOverSlice S` is `Over.mk` of `toBase (ofOver T)`. -/
theorem ofOverSlice_obj (S : Scheme.{u}) (T : Over S) :
    (ofOverSlice S).obj T = Over.mk (toBase (ofOver T)) :=
  sorry

/-- The fibre product of `ofOver X` and `ofOver Y` over `S`, as an algebraic space over `S`. -/
def ofOverPullback {S : Scheme.{u}} (X Y : Over S) : AlgebraicSpace S :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOver
    (toBase (ofOver X)) (toBase (ofOver Y))
    (ofOver (Over.mk (𝟙 S))).isSheaf (ofOver (Over.mk (𝟙 S))).representableDiagonal

/-- `ofOverPullback X Y` is the sheaf fibre product of the `toBase` morphisms. -/
theorem ofOverPullback_eq {S : Scheme.{u}} (X Y : Over S) :
    ofOverPullback X Y =
      AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOver
        (toBase (ofOver X)) (toBase (ofOver Y))
        (ofOver (Over.mk (𝟙 S))).isSheaf (ofOver (Over.mk (𝟙 S))).representableDiagonal :=
  sorry

/-- The comparison from the chosen fibre product of `toBase` maps to `ofOverPullback`. -/
def ofOverPullbackHom {S : Scheme.{u}} (X Y : Over S) :
    Limits.pullback (toBase (ofOver X)) (toBase (ofOver Y)) ⟶ ofOverPullback X Y :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackLift
    (toBase (ofOver X)) (toBase (ofOver Y))
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- `ofOverPullbackHom X Y` is the mediating map induced by the chosen pullback projections. -/
theorem ofOverPullbackHom_eq {S : Scheme.{u}} (X Y : Over S) :
    ofOverPullbackHom X Y =
      AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackLift
        (toBase (ofOver X)) (toBase (ofOver Y))
        (pullback.fst _ _) (pullback.snd _ _) pullback.condition :=
  sorry

/-- The first projection of `ofOverPullback X Y`. -/
def ofOverPullbackFst {S : Scheme.{u}} (X Y : Over S) :
    ofOverPullback X Y ⟶ ofOver X :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverFst
    (toBase (ofOver X)) (toBase (ofOver Y))
    (ofOver (Over.mk (𝟙 S))).isSheaf (ofOver (Over.mk (𝟙 S))).representableDiagonal

/-- The second projection of `ofOverPullback X Y`. -/
def ofOverPullbackSnd {S : Scheme.{u}} (X Y : Over S) :
    ofOverPullback X Y ⟶ ofOver Y :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverSnd
    (toBase (ofOver X)) (toBase (ofOver Y))
    (ofOver (Over.mk (𝟙 S))).isSheaf (ofOver (Over.mk (𝟙 S))).representableDiagonal

/-- The morphism `T ⟶ U` associated to a `T`-point of `ofOver U`. -/
def ofOverPoint {S : Scheme.{u}} {U : Over S} {T : (Over S)ᵒᵖ}
    (p : (ofOver U).functorOfPoints.obj T) : T.unop ⟶ U :=
  (yonedaEquiv.symm p).app (op T.unop) (𝟙 _)

/-- The identity `T`-point of `ofOver T`. -/
def ofOverIdPoint {S : Scheme.{u}} (T : Over S) :
    (ofOver T).functorOfPoints.obj (op T) :=
  yonedaEquiv (𝟙 (yoneda.obj T))

/-- The comparison from the algebraic-space fibre product to `ofOver (X ⊗ Y)`. -/
def tensorComparison {S : Scheme.{u}} (X Y : Over S) :
    ofOverPullback X Y ⟶ ofOver (X ⊗ Y) where
  app T := ↾fun p ↦
    (ofOverMap
      (lift (ofOverPoint ((ofOverPullbackFst X Y).app T p))
        (ofOverPoint ((ofOverPullbackSnd X Y).app T p)))).app T
      (ofOverIdPoint T.unop)
  naturality := sorry

/-- The component of `tensorComparison X Y` at a test scheme. -/
theorem tensorComparison_app {S : Scheme.{u}} (X Y : Over S) (T : (Over S)ᵒᵖ)
    (p : (ofOverPullback X Y).functorOfPoints.obj T) :
    (tensorComparison X Y).app T p =
      (ofOverMap
        (lift (ofOverPoint ((ofOverPullbackFst X Y).app T p))
          (ofOverPoint ((ofOverPullbackSnd X Y).app T p)))).app T
        (ofOverIdPoint T.unop) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeRealization
