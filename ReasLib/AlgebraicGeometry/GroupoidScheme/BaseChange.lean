module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Base change of groupoid schemes

This module defines base change for groupoid schemes, together with the canonical
comparison that regards a groupoid scheme over `S'` as one over `S` along `f : S' ⟶ S`.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The base-changed composition map, transported through preservation of pullbacks. -/
def baseChangeComposition {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    pullback ((Over.pullback f).map G.s) ((Over.pullback f).map G.t) ⟶
      (Over.pullback f).obj G.R :=
  (PreservesPullback.iso (Over.pullback f) G.s G.t).inv ≫ (Over.pullback f).map G.c

/-- Base-changed composition has the base-changed source of its second arrow. -/
theorem baseChangeCompSource {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    baseChangeComposition f G ≫ (Over.pullback f).map G.s =
      pullback.snd ((Over.pullback f).map G.s) ((Over.pullback f).map G.t) ≫
        (Over.pullback f).map G.s := sorry

/-- Base-changed composition has the base-changed target of its first arrow. -/
theorem baseChangeCompTarget {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    baseChangeComposition f G ≫ (Over.pullback f).map G.t =
      pullback.fst ((Over.pullback f).map G.s) ((Over.pullback f).map G.t) ≫
        (Over.pullback f).map G.t := sorry

/-- The base-changed unit has the required source. -/
theorem baseChangeUnitSource {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (Over.pullback f).map G.e ≫ (Over.pullback f).map G.s =
      𝟙 ((Over.pullback f).obj G.U) := sorry

/-- The base-changed unit has the required target. -/
theorem baseChangeUnitTarget {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (Over.pullback f).map G.e ≫ (Over.pullback f).map G.t =
      𝟙 ((Over.pullback f).obj G.U) := sorry

/-- The base-changed inverse exchanges source and target. -/
theorem baseChangeInvSource {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (Over.pullback f).map G.i ≫ (Over.pullback f).map G.s =
      (Over.pullback f).map G.t := sorry

/-- The base-changed inverse exchanges target and source. -/
theorem baseChangeInvTarget {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (Over.pullback f).map G.i ≫ (Over.pullback f).map G.t =
      (Over.pullback f).map G.s := sorry

/-- Base-changed composition is associative on every scheme of points. -/
theorem baseChangeAssociativity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    ∀ {T : Over S'} (a b d : T ⟶ (Over.pullback f).obj G.R)
      (h_ab : a ≫ (Over.pullback f).map G.s = b ≫ (Over.pullback f).map G.t)
      (h_bd : b ≫ (Over.pullback f).map G.s = d ≫ (Over.pullback f).map G.t)
      (h_ab_d : (pullback.lift a b h_ab ≫ baseChangeComposition f G) ≫
        (Over.pullback f).map G.s = d ≫ (Over.pullback f).map G.t)
      (h_a_bd : a ≫ (Over.pullback f).map G.s =
        (pullback.lift b d h_bd ≫ baseChangeComposition f G) ≫
          (Over.pullback f).map G.t),
      pullback.lift (pullback.lift a b h_ab ≫ baseChangeComposition f G) d h_ab_d ≫
          baseChangeComposition f G =
        pullback.lift a (pullback.lift b d h_bd ≫ baseChangeComposition f G) h_a_bd ≫
          baseChangeComposition f G := sorry

/-- Base-changed composition has the right identity law on every scheme of points. -/
theorem baseChangeRightIdentity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    ∀ {T : Over S'} (a : T ⟶ (Over.pullback f).obj G.R)
      (h : a ≫ (Over.pullback f).map G.s =
        ((a ≫ (Over.pullback f).map G.s) ≫ (Over.pullback f).map G.e) ≫
          (Over.pullback f).map G.t),
      pullback.lift a
          ((a ≫ (Over.pullback f).map G.s) ≫ (Over.pullback f).map G.e) h ≫
        baseChangeComposition f G = a := sorry

/-- Base-changed composition has the left identity law on every scheme of points. -/
theorem baseChangeLeftIdentity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    ∀ {T : Over S'} (a : T ⟶ (Over.pullback f).obj G.R)
      (h : ((a ≫ (Over.pullback f).map G.t) ≫ (Over.pullback f).map G.e) ≫
          (Over.pullback f).map G.s = a ≫ (Over.pullback f).map G.t),
      pullback.lift
          ((a ≫ (Over.pullback f).map G.t) ≫ (Over.pullback f).map G.e) a h ≫
        baseChangeComposition f G = a := sorry

/-- An arrow followed by its base-changed inverse composes to the identity at its target. -/
theorem baseChangeInverseComp {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    ∀ {T : Over S'} (a : T ⟶ (Over.pullback f).obj G.R)
      (h : a ≫ (Over.pullback f).map G.s =
        (a ≫ (Over.pullback f).map G.i) ≫ (Over.pullback f).map G.t),
      pullback.lift a (a ≫ (Over.pullback f).map G.i) h ≫ baseChangeComposition f G =
        (a ≫ (Over.pullback f).map G.t) ≫ (Over.pullback f).map G.e := sorry

/-- A base-changed inverse followed by its arrow composes to the identity at its source. -/
theorem baseChangeCompInverse {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    ∀ {T : Over S'} (a : T ⟶ (Over.pullback f).obj G.R)
      (h : (a ≫ (Over.pullback f).map G.i) ≫ (Over.pullback f).map G.s =
        a ≫ (Over.pullback f).map G.t),
      pullback.lift (a ≫ (Over.pullback f).map G.i) a h ≫ baseChangeComposition f G =
        (a ≫ (Over.pullback f).map G.s) ≫ (Over.pullback f).map G.e := sorry

/-- Base change of a groupoid scheme along a morphism of base schemes. -/
def baseChange {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    GroupoidScheme S' where
  U := (Over.pullback f).obj G.U
  R := (Over.pullback f).obj G.R
  s := (Over.pullback f).map G.s
  t := (Over.pullback f).map G.t
  e := (Over.pullback f).map G.e
  i := (Over.pullback f).map G.i
  c := baseChangeComposition f G
  comp_source := baseChangeCompSource f G
  comp_target := baseChangeCompTarget f G
  identity_source := baseChangeUnitSource f G
  identity_target := baseChangeUnitTarget f G
  inverse_source := baseChangeInvSource f G
  inverse_target := baseChangeInvTarget f G
  associativity := baseChangeAssociativity f G
  right_identity := baseChangeRightIdentity f G
  left_identity := baseChangeLeftIdentity f G
  inverse_comp := baseChangeInverseComp f G
  comp_inverse := baseChangeCompInverse f G

/-- The object scheme of a base-changed groupoid is the pullback of the original object scheme. -/
theorem baseChange_U {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).U = (Over.pullback f).obj G.U := sorry

/-- The arrow scheme of a base-changed groupoid is the pullback of the original arrow scheme. -/
theorem baseChange_R {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).R = (Over.pullback f).obj G.R := sorry

/-- The source map of a base-changed groupoid is the base-changed source map. -/
theorem baseChange_s {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).s = (Over.pullback f).map G.s := sorry

/-- The target map of a base-changed groupoid is the base-changed target map. -/
theorem baseChange_t {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).t = (Over.pullback f).map G.t := sorry

/-- The composition of a base-changed groupoid is transported by the pullback comparison. -/
theorem baseChange_c {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).c = baseChangeComposition f G := sorry

/-- The unit of a base-changed groupoid is the base-changed unit. -/
theorem baseChange_e {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).e = (Over.pullback f).map G.e := sorry

/-- The inverse of a base-changed groupoid is the base-changed inverse. -/
theorem baseChange_i {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    (baseChange f G).i = (Over.pullback f).map G.i := sorry

/-- The underlying comparison map for composable arrows lies over the ambient base. -/
theorem changeBaseComposable_condition {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ((PreservesPullback.iso (Over.forget S) ((Over.map f).map G.s)
          ((Over.map f).map G.t)).hom ≫
        (PreservesPullback.iso (Over.forget S') G.s G.t).inv) ≫
      ((Over.map f).obj (pullback G.s G.t)).hom =
        (pullback ((Over.map f).map G.s) ((Over.map f).map G.t)).hom := sorry

/-- The canonical comparison from composable arrows after changing the ambient base to the
ambient-base image of the original composable-arrow object. -/
def changeBaseComposable {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    pullback ((Over.map f).map G.s) ((Over.map f).map G.t) ⟶
      (Over.map f).obj (pullback G.s G.t) :=
  Over.homMk
    ((PreservesPullback.iso (Over.forget S) ((Over.map f).map G.s)
          ((Over.map f).map G.t)).hom ≫
      (PreservesPullback.iso (Over.forget S') G.s G.t).inv)
    (changeBaseComposable_condition f G)

/-- Composition after changing the ambient base has the required source. -/
theorem changeBaseCompSource {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (changeBaseComposable f G ≫ (Over.map f).map G.c) ≫ (Over.map f).map G.s =
      pullback.snd ((Over.map f).map G.s) ((Over.map f).map G.t) ≫
        (Over.map f).map G.s := sorry

/-- Composition after changing the ambient base has the required target. -/
theorem changeBaseCompTarget {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (changeBaseComposable f G ≫ (Over.map f).map G.c) ≫ (Over.map f).map G.t =
      pullback.fst ((Over.map f).map G.s) ((Over.map f).map G.t) ≫
        (Over.map f).map G.t := sorry

/-- The unit retains its source after changing the ambient base. -/
theorem changeBaseUnitSource {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (Over.map f).map G.e ≫ (Over.map f).map G.s = 𝟙 ((Over.map f).obj G.U) := sorry

/-- The unit retains its target after changing the ambient base. -/
theorem changeBaseUnitTarget {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (Over.map f).map G.e ≫ (Over.map f).map G.t = 𝟙 ((Over.map f).obj G.U) := sorry

/-- Inversion exchanges source and target after changing the ambient base. -/
theorem changeBaseInvSource {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (Over.map f).map G.i ≫ (Over.map f).map G.s = (Over.map f).map G.t := sorry

/-- Inversion exchanges target and source after changing the ambient base. -/
theorem changeBaseInvTarget {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    (Over.map f).map G.i ≫ (Over.map f).map G.t = (Over.map f).map G.s := sorry

/-- Composition remains associative after changing the ambient base. -/
theorem changeBaseAssociativity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ∀ {T : Over S} (a b d : T ⟶ (Over.map f).obj G.R)
      (h_ab : a ≫ (Over.map f).map G.s = b ≫ (Over.map f).map G.t)
      (h_bd : b ≫ (Over.map f).map G.s = d ≫ (Over.map f).map G.t)
      (h_ab_d :
        (pullback.lift a b h_ab ≫ (changeBaseComposable f G ≫ (Over.map f).map G.c)) ≫
          (Over.map f).map G.s = d ≫ (Over.map f).map G.t)
      (h_a_bd : a ≫ (Over.map f).map G.s =
        (pullback.lift b d h_bd ≫ (changeBaseComposable f G ≫ (Over.map f).map G.c)) ≫
          (Over.map f).map G.t),
      pullback.lift
            (pullback.lift a b h_ab ≫
              (changeBaseComposable f G ≫ (Over.map f).map G.c))
            d h_ab_d ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) =
        pullback.lift a
            (pullback.lift b d h_bd ≫
              (changeBaseComposable f G ≫ (Over.map f).map G.c))
            h_a_bd ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) := sorry

/-- Composition retains the right identity law after changing the ambient base. -/
theorem changeBaseRightIdentity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ∀ {T : Over S} (a : T ⟶ (Over.map f).obj G.R)
      (h : a ≫ (Over.map f).map G.s =
        ((a ≫ (Over.map f).map G.s) ≫ (Over.map f).map G.e) ≫ (Over.map f).map G.t),
      pullback.lift a ((a ≫ (Over.map f).map G.s) ≫ (Over.map f).map G.e) h ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) = a := sorry

/-- Composition retains the left identity law after changing the ambient base. -/
theorem changeBaseLeftIdentity {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ∀ {T : Over S} (a : T ⟶ (Over.map f).obj G.R)
      (h : ((a ≫ (Over.map f).map G.t) ≫ (Over.map f).map G.e) ≫
          (Over.map f).map G.s = a ≫ (Over.map f).map G.t),
      pullback.lift ((a ≫ (Over.map f).map G.t) ≫ (Over.map f).map G.e) a h ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) = a := sorry

/-- An arrow followed by its inverse retains the identity law after changing the ambient base. -/
theorem changeBaseInverseComp {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ∀ {T : Over S} (a : T ⟶ (Over.map f).obj G.R)
      (h : a ≫ (Over.map f).map G.s =
        (a ≫ (Over.map f).map G.i) ≫ (Over.map f).map G.t),
      pullback.lift a (a ≫ (Over.map f).map G.i) h ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) =
        (a ≫ (Over.map f).map G.t) ≫ (Over.map f).map G.e := sorry

/-- An inverse followed by its arrow retains the identity law after changing the ambient base. -/
theorem changeBaseCompInverse {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S') :
    ∀ {T : Over S} (a : T ⟶ (Over.map f).obj G.R)
      (h : (a ≫ (Over.map f).map G.i) ≫ (Over.map f).map G.s =
        a ≫ (Over.map f).map G.t),
      pullback.lift (a ≫ (Over.map f).map G.i) a h ≫
          (changeBaseComposable f G ≫ (Over.map f).map G.c) =
        (a ≫ (Over.map f).map G.s) ≫ (Over.map f).map G.e := sorry

/-- Regard a groupoid scheme over `S'` as a groupoid scheme over `S` along `f : S' ⟶ S`. -/
def changeBase {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    GroupoidScheme S where
  U := (Over.map f).obj G.U
  R := (Over.map f).obj G.R
  s := (Over.map f).map G.s
  t := (Over.map f).map G.t
  e := (Over.map f).map G.e
  i := (Over.map f).map G.i
  c := changeBaseComposable f G ≫ (Over.map f).map G.c
  comp_source := changeBaseCompSource f G
  comp_target := changeBaseCompTarget f G
  identity_source := changeBaseUnitSource f G
  identity_target := changeBaseUnitTarget f G
  inverse_source := changeBaseInvSource f G
  inverse_target := changeBaseInvTarget f G
  associativity := changeBaseAssociativity f G
  right_identity := changeBaseRightIdentity f G
  left_identity := changeBaseLeftIdentity f G
  inverse_comp := changeBaseInverseComp f G
  comp_inverse := changeBaseCompInverse f G

/-- The object scheme of a groupoid regarded over a larger base is the mapped object scheme. -/
theorem changeBase_U {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).U = (Over.map f).obj G.U := sorry

/-- The arrow scheme of a groupoid regarded over a larger base is the mapped arrow scheme. -/
theorem changeBase_R {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).R = (Over.map f).obj G.R := sorry

/-- The source map of a groupoid regarded over a larger base is the mapped source map. -/
theorem changeBase_s {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).s = (Over.map f).map G.s := sorry

/-- The target map of a groupoid regarded over a larger base is the mapped target map. -/
theorem changeBase_t {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).t = (Over.map f).map G.t := sorry

/-- The composition map over the larger base uses the canonical composable-arrow comparison. -/
theorem changeBase_c {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).c = changeBaseComposable f G ≫ (Over.map f).map G.c := sorry

/-- The unit map over the larger base is the mapped unit map. -/
theorem changeBase_e {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).e = (Over.map f).map G.e := sorry

/-- The inverse map over the larger base is the mapped inverse map. -/
theorem changeBase_i {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S') :
    (changeBase f G).i = (Over.map f).map G.i := sorry

/-- The canonical projection commutes with the source maps. -/
theorem baseChangeProjectionMapSource {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    (changeBase f (baseChange f G)).s ≫ (Over.mapPullbackAdj f).counit.app G.U =
      (Over.mapPullbackAdj f).counit.app G.R ≫ G.s := sorry

/-- The canonical projection commutes with the target maps. -/
theorem baseChangeProjectionMapTarget {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    (changeBase f (baseChange f G)).t ≫ (Over.mapPullbackAdj f).counit.app G.U =
      (Over.mapPullbackAdj f).counit.app G.R ≫ G.t := sorry

/-- The canonical projection commutes with composition. -/
theorem baseChangeProjectionMapComposition {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    (changeBase f (baseChange f G)).c ≫ (Over.mapPullbackAdj f).counit.app G.R =
      @composableMap S (changeBase f (baseChange f G)) G
          ((Over.mapPullbackAdj f).counit.app G.U)
          ((Over.mapPullbackAdj f).counit.app G.R)
          (baseChangeProjectionMapSource f G) (baseChangeProjectionMapTarget f G) ≫
        G.c := sorry

/-- After transporting `baseChange f G` back to the base `S` via `Over.map f`, the canonical
object and arrow projections define an ordinary morphism of groupoid schemes. -/
def baseChangeProjection {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupoidScheme S) :
    Hom (changeBase f (baseChange f G)) G where
  obj := (Over.mapPullbackAdj f).counit.app G.U
  arrow := (Over.mapPullbackAdj f).counit.app G.R
  map_s := baseChangeProjectionMapSource f G
  map_t := baseChangeProjectionMapTarget f G
  map_c := baseChangeProjectionMapComposition f G

/-- The object component of the base-change projection is the pullback-adjunction counit. -/
theorem baseChangeProjection_obj {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    (baseChangeProjection f G).obj = (Over.mapPullbackAdj f).counit.app G.U := sorry

/-- The arrow component of the base-change projection is the pullback-adjunction counit. -/
theorem baseChangeProjection_arrow {S S' : Scheme.{u}} (f : S' ⟶ S)
    (G : GroupoidScheme S) :
    (baseChangeProjection f G).arrow = (Over.mapPullbackAdj f).counit.app G.R := sorry

end AlgebraicGeometry.GroupoidScheme
