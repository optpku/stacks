module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Pair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input

/-!
# Morphisms into the finite-part functor

A morphism of algebraic spaces `f : X ⟶ Y` over a scheme `S` determines the
structure map `(X/Y)_fin ⟶ Y` and a canonical identification of morphisms
`T ⟶ (X/Y)_fin` with descended finite-open pairs `(a, Z)` over an algebraic space `T`,
recorded by the morphism `a` and the open of `|T ×_Y X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The structure morphism `(X/Y)_fin ⟶ Y`, sending a pair `(a, Z)` to the
`Y`-section `a`. -/
def toY (f : X ⟶ Y) : finitePart f ⟶ Y.functorOfPoints where
  app T := TypeCat.ofHom fun p ↦ (finitePart_obj_equiv f T.unop p).a_elem
  naturality := sorry

/-- Components of `toY f` recover `Point.a_elem`. -/
theorem toY_app (f : X ⟶ Y) (T : (Over S)ᵒᵖ) (p : (finitePart f).obj T) :
    (toY f).app T p = (finitePart_obj_equiv f T.unop p).a_elem :=
  rfl

/-- On a pair `(a, Z)`, the structure morphism records `a` as `Point.a_elem`. -/
theorem toY_spec (f : X ⟶ Y) {T : Over S} (p : Point f T) :
    (toY f).app (op T) ((finitePart_obj_equiv f T).symm p) = p.a_elem := by
  change (finitePart_obj_equiv f T ((finitePart_obj_equiv f T).symm p)).a_elem = p.a_elem
  rw [Equiv.apply_symm_apply]

/-- Convert a finite-open pair over a scheme, viewed as an algebraic space, to a
scheme-level finite-part pair. -/
def toPoint {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) : Point f U :=
  Point.of p.a p.Z.pointsOpens ((SubspacePoint.of p.a p.Z p.finite_pr).toPoint_isFinite)

/-- Convert a scheme-level finite-part pair to a finite-open pair over the represented
algebraic space. -/
def ofPoint {f : X ⟶ Y} {U : Over S} (p : Point f U) : FinitePart f (ofOver U) :=
  FinitePart.of p.a (OpenSubspace.fromOpens p.Z) p.isFinite

/-- `toPoint` preserves the morphism to `Y`. -/
theorem toPoint_a {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) :
    (toPoint p).a = p.a :=
  rfl

/-- `toPoint` records the points-open of the open subspace. -/
theorem toPoint_Z {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) :
    (toPoint p).Z = p.Z.pointsOpens :=
  rfl

/-- `ofPoint` preserves the morphism to `Y`. -/
theorem ofPoint_a {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    (ofPoint p).a = p.a :=
  rfl

/-- `ofPoint` realises the open as `OpenSubspace.fromOpens`. -/
theorem ofPoint_Z {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    (ofPoint p).Z = OpenSubspace.fromOpens p.Z :=
  rfl

/-- The presheaf morphism `T ⟶ (X/Y)_fin` induced by a finite-open pair, sending a
`U`-point of `T` to the inverse image of `(a, Z)`. -/
def homOfPair {T : AlgebraicSpace S} {f : X ⟶ Y} (p : FinitePart f T) :
    T.functorOfPoints ⟶ finitePart f where
  app U :=
    TypeCat.ofHom fun s ↦
      (finitePart_obj_equiv f U.unop).symm (toPoint (p.map (yonedaEquiv.symm s)))
  naturality := sorry

/-- Components of `homOfPair` restrict the pair and shrink the resulting
scheme-level pair. -/
theorem homOfPair_app {T : AlgebraicSpace S} {f : X ⟶ Y} (p : FinitePart f T)
    (U : (Over S)ᵒᵖ) (s : T.functorOfPoints.obj U) :
    (homOfPair p).app U s =
      (finitePart_obj_equiv f U.unop).symm
        (toPoint (p.map (yonedaEquiv.symm s))) :=
  rfl

/-- The morphism `T ⟶ Y` obtained by composing a presheaf map
`T ⟶ (X/Y)_fin` with the structure morphism `toY`. -/
def homToY {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : T ⟶ Y :=
  (η ≫ toY f : T.functorOfPoints ⟶ Y.functorOfPoints)

/-- `homToY η` is the functor-category composite of `η` with `toY f`. -/
theorem homToY_eq {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    homToY η = (η ≫ toY f : T.functorOfPoints ⟶ Y.functorOfPoints) :=
  rfl

/-- The scheme-level pair obtained by evaluating a presheaf morphism
`T ⟶ (X/Y)_fin` on a chosen atlas of `T`. -/
private def pointOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : Point f (AtlasInput.scheme T) :=
  finitePart_obj_equiv f (AtlasInput.scheme T) (yonedaEquiv (AtlasInput.map T ≫ η))

/-- The maps `pr₀ ≫ AtlasInput.map T` and `pr₁` out of `U ×_Y X` agree over `Y`, so they
induce a comparison `U ×_Y X ⟶ T ×_Y X`. -/
private theorem compareToPullback_condition {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (pullback.fst (pointOfHom η).a f ≫ AtlasInput.map T) ≫ homToY η =
      pullback.snd (pointOfHom η).a f ≫ f :=
  sorry

/-- The comparison `U ×_Y X ⟶ T ×_Y X` induced by the chosen atlas of `T` and
the structure morphism of `η`. -/
private def compareToPullback {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    pullback (pointOfHom η).a f ⟶ pullback (homToY η) f :=
  pullback.lift (pullback.fst (pointOfHom η).a f ≫ AtlasInput.map T)
    (pullback.snd (pointOfHom η).a f) (compareToPullback_condition η)

/-- The image of the atlas-level open along `compareToPullback` is open. -/
private theorem isOpen_opensOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    IsOpen (Points.map (compareToPullback η) '' (pointOfHom η).Z.carrier) :=
  sorry

/-- The open of `|T ×_Y X|` obtained by transporting the atlas-level open of
`η` along the comparison to `pullback (homToY η) f`. -/
@[no_expose]
def opensOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    Opens (Points (pullback (homToY η) f)) :=
  Opens.mk (Points.map (compareToPullback η) '' (pointOfHom η).Z.carrier)
    (isOpen_opensOfHom η)

/-- The open subspace cut out by `opensOfHom η` is finite over `T`. -/
theorem opensOfHom_isFinite {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    IsFinite
      ((OpenSubspace.fromOpens (opensOfHom η)).ι ≫ pullback.fst (homToY η) f) :=
  sorry

/-- A finite-open pair over an algebraic space `T`, recorded by the morphism `a : T ⟶ Y`
and the open of `|T ×_Y X|` rather than a chosen open-subspace presentation. -/
structure Descended (f : X ⟶ Y) (T : AlgebraicSpace S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : T ⟶ Y
  /-- The open `Z ⊂ |T ×_Y X|`. -/
  Z : Opens (Points (pullback a f))
  /-- The restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
  isFinite : IsFinite ((OpenSubspace.fromOpens Z).ι ≫ pullback.fst a f)

namespace Descended

/-- Build a descended finite-open pair from a morphism `a : T ⟶ Y`, an open of
`|T ×_Y X|`, and finiteness of the restricted first projection. -/
def of {T : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (Z : Opens (Points (pullback a f)))
    (h : IsFinite ((OpenSubspace.fromOpens Z).ι ≫ pullback.fst a f)) :
    Descended f T where
  a := a
  Z := Z
  isFinite := h

/-- A descended pair consists of an open of `|T ×_Y X|` whose `fromOpens` subspace
is finite over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (OpenSubspace.fromOpens p.Z).pointsSet = p.Z ∧
      IsFinite ((OpenSubspace.fromOpens p.Z).ι ≫ pullback.fst p.a f) :=
  ⟨OpenSubspace.fromOpens_pointsSet p.Z, p.isFinite⟩

/-- The open-subspace presentation of a descended pair, taking the open subspace cut out
by the point-set open. -/
def toPair {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    FinitePart f T :=
  FinitePart.of p.a (OpenSubspace.fromOpens p.Z) p.isFinite

/-- `toPair` preserves the morphism to `Y`. -/
theorem toPair_a {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (toPair p).a = p.a :=
  rfl

/-- `toPair` realises the open as `OpenSubspace.fromOpens`. -/
theorem toPair_Z {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (toPair p).Z = OpenSubspace.fromOpens p.Z :=
  rfl

/-- The descended finite-open pair associated to a presheaf morphism `T ⟶ (X/Y)_fin`. -/
def ofHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : Descended f T :=
  of (homToY η) (opensOfHom η) (opensOfHom_isFinite η)

/-- The morphism to `Y` of `ofHom η` is `η` followed by `toY`. -/
theorem ofHom_a {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (ofHom η).a = homToY η :=
  rfl

/-- The open of `ofHom η` is `opensOfHom η`. -/
theorem ofHom_Z {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (ofHom η).Z = opensOfHom η :=
  rfl

end Descended

/-- Restricting the descended pair of a presheaf morphism recovers that morphism. -/
theorem homOfPair_toPair_ofHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    homOfPair (Descended.ofHom η).toPair = η :=
  sorry

/-- Descending the restrictions of a finite-open pair recovers that pair. -/
theorem ofHom_homOfPair_toPair {T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : Descended f T) :
    Descended.ofHom (homOfPair p.toPair) = p :=
  sorry

/-- Presheaf morphisms `T ⟶ (X/Y)_fin` are canonically descended finite-open pairs over
`T`. -/
def homEquiv {T : AlgebraicSpace S} (f : X ⟶ Y) :
    (T.functorOfPoints ⟶ finitePart f) ≃ Descended f T where
  toFun := Descended.ofHom
  invFun p := homOfPair p.toPair
  left_inv := homOfPair_toPair_ofHom
  right_inv := ofHom_homOfPair_toPair

/-- `homEquiv` sends a presheaf morphism to `Descended.ofHom`. -/
theorem homEquiv_apply {T : AlgebraicSpace S} (f : X ⟶ Y)
    (η : T.functorOfPoints ⟶ finitePart f) :
    homEquiv f η = Descended.ofHom η :=
  rfl

/-- The inverse of `homEquiv` sends a descended pair to `homOfPair` of its
`fromOpens` presentation. -/
theorem homEquiv_symm_apply {T : AlgebraicSpace S} (f : X ⟶ Y)
    (p : Descended f T) :
    (homEquiv f).symm p = homOfPair p.toPair :=
  rfl

end FinitePart

/-- Morphisms from an algebraic space to the finite-part fppf sheaf are canonically
in bijection with finite-open pairs over that space. -/
def finitePart_homEquiv {S : Scheme.{u}} {X Y T : AlgebraicSpace S} (f : X ⟶ Y) :
    (toSmallSheaf T ⟶ FinitePart.sheaf f) ≃ FinitePart.Descended f T :=
  Sheaf.homEquiv.trans (FinitePart.homEquiv f)

/-- Applying `finitePart_homEquiv` recovers the descended finite-open pair of the
underlying presheaf morphism. -/
theorem finitePart_homEquiv_apply {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (f : X ⟶ Y) (η : toSmallSheaf T ⟶ FinitePart.sheaf f) :
    finitePart_homEquiv f η = FinitePart.Descended.ofHom (Sheaf.homEquiv η) :=
  rfl

/-- On a scheme `U` over `S`, morphisms of fppf sheaves `U ⟶ (X/Y)_fin` are
scheme-level finite-part pairs. -/
def finitePart_homEquiv_ofOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (U : Over S) :
    (toSmallSheaf (ofOver U) ⟶ FinitePart.sheaf f) ≃ FinitePart.Point f U :=
  Sheaf.homEquiv.trans (yonedaEquiv.trans (finitePart_obj_equiv f U))

end AlgebraicGeometry.AlgebraicSpace
