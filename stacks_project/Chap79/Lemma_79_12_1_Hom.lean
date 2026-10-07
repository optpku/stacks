module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap79.«79_12_0_1_FinitePart»
public import stacks_project.Chap79.«79_12_0_2»

/-!
# Morphisms into the finite-part functor

A morphism of algebraic spaces `f : X ⟶ Y` over a scheme `S` determines the
structure map `(X/Y)_fin ⟶ Y` and a canonical identification of morphisms
`T ⟶ (X/Y)_fin` with descended 04PC pairs `(a, Z)` over an algebraic space `T`,
recorded by the morphism `a` and the open of `|T ×_Y X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A chosen scheme atlas of an algebraic space, extracted from the defining
existence field. -/
def atlasOver {S : Scheme.{u}} (X : AlgebraicSpace S) : Over S :=
  Classical.choose X.atlas

/-- The chosen representable étale atlas morphism of an algebraic space. -/
def atlasHom {S : Scheme.{u}} (X : AlgebraicSpace S) : ofOver (atlasOver X) ⟶ X :=
  Classical.choose (Classical.choose_spec X.atlas)

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
  sorry

/-- On a pair `(a, Z)`, the structure morphism records `a` as `Point.a_elem`. -/
theorem toY_spec (f : X ⟶ Y) {T : Over S} (p : Point f T) :
    (toY f).app (op T) ((finitePart_obj_equiv f T).symm p) = p.a_elem :=
  sorry

/-- Finiteness of the restricted first projection after replacing an open
subspace by the open subspace cut out by its points. -/
theorem toPoint_isFinite {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) :
    IsFinite
      ((OpenSubspace.ofOpens p.Z.pointsOpens).ι ≫ pullback.fst p.a f) :=
  sorry

/-- Convert a 04PC pair over a scheme, viewed as an algebraic space, to a
scheme-level finite-part pair. -/
def toPoint {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) : Point f U :=
  Point.of p.a p.Z.pointsOpens (toPoint_isFinite p)

/-- Convert a scheme-level finite-part pair to a 04PC pair over the represented
algebraic space. -/
def ofPoint {f : X ⟶ Y} {U : Over S} (p : Point f U) : FinitePart f (ofOver U) :=
  FinitePart.of p.a (OpenSubspace.ofOpens p.Z) p.isFinite

/-- `toPoint` preserves the morphism to `Y`. -/
theorem toPoint_a {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) :
    (toPoint p).a = p.a :=
  sorry

/-- `toPoint` records the points-open of the open subspace. -/
theorem toPoint_Z {f : X ⟶ Y} {U : Over S} (p : FinitePart f (ofOver U)) :
    (toPoint p).Z = p.Z.pointsOpens :=
  sorry

/-- `ofPoint` preserves the morphism to `Y`. -/
theorem ofPoint_a {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    (ofPoint p).a = p.a :=
  sorry

/-- `ofPoint` realises the open as `OpenSubspace.ofOpens`. -/
theorem ofPoint_Z {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    (ofPoint p).Z = OpenSubspace.ofOpens p.Z :=
  sorry

/-- The presheaf morphism `T ⟶ (X/Y)_fin` induced by a 04PC pair, sending a
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
  sorry

/-- The morphism `T ⟶ Y` obtained by composing a presheaf map
`T ⟶ (X/Y)_fin` with the structure morphism `toY`. -/
def homToY {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : T ⟶ Y :=
  (η ≫ toY f : T.functorOfPoints ⟶ Y.functorOfPoints)

/-- `homToY η` is the functor-category composite of `η` with `toY f`. -/
theorem homToY_eq {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    homToY η = (η ≫ toY f : T.functorOfPoints ⟶ Y.functorOfPoints) :=
  sorry

/-- The scheme-level pair obtained by evaluating a presheaf morphism
`T ⟶ (X/Y)_fin` on a chosen atlas of `T`. -/
def pointOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : Point f (atlasOver T) :=
  finitePart_obj_equiv f (atlasOver T) (yonedaEquiv (atlasHom T ≫ η))

/-- The maps `pr₀ ≫ atlasHom T` and `pr₁` out of `U ×_Y X` agree over `Y`, so they
induce a comparison `U ×_Y X ⟶ T ×_Y X`. -/
theorem compareToPullback_condition {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (pullback.fst (pointOfHom η).a f ≫ atlasHom T) ≫ homToY η =
      pullback.snd (pointOfHom η).a f ≫ f :=
  sorry

/-- The comparison `U ×_Y X ⟶ T ×_Y X` induced by the chosen atlas of `T` and
the structure morphism of `η`. -/
def compareToPullback {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    pullback (pointOfHom η).a f ⟶ pullback (homToY η) f :=
  pullback.lift (pullback.fst (pointOfHom η).a f ≫ atlasHom T)
    (pullback.snd (pointOfHom η).a f) (compareToPullback_condition η)

/-- The image of the atlas-level open along `compareToPullback` is open. -/
theorem isOpen_opensOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    IsOpen (Points.map (compareToPullback η) '' (pointOfHom η).Z.carrier) :=
  sorry

/-- The open of `|T ×_Y X|` obtained by transporting the atlas-level open of
`η` along the comparison to `pullback (homToY η) f`. -/
def opensOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    Opens (Points (pullback (homToY η) f)) :=
  Opens.mk (Points.map (compareToPullback η) '' (pointOfHom η).Z.carrier)
    (isOpen_opensOfHom η)

/-- The open subspace cut out by `opensOfHom η` is finite over `T`. -/
theorem pairOfHom_isFinite {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    IsFinite
      ((OpenSubspace.ofOpens (opensOfHom η)).ι ≫ pullback.fst (homToY η) f) :=
  sorry

/-- The 04PC pair associated to a presheaf morphism `T ⟶ (X/Y)_fin`. -/
def pairOfHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : FinitePart f T :=
  FinitePart.of (homToY η) (OpenSubspace.ofOpens (opensOfHom η))
    (pairOfHom_isFinite η)

/-- The morphism to `Y` of `pairOfHom η` is `η` followed by `toY`. -/
theorem pairOfHom_a {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (pairOfHom η).a = homToY η :=
  sorry

/-- The open subspace of `pairOfHom η` is cut out by `opensOfHom η`. -/
theorem pairOfHom_Z {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (pairOfHom η).Z = OpenSubspace.ofOpens (opensOfHom η) :=
  sorry

/-- A 04PC pair over an algebraic space `T`, recorded by the morphism `a : T ⟶ Y`
and the open of `|T ×_Y X|` rather than a chosen open-subspace presentation. -/
structure Descended (f : X ⟶ Y) (T : AlgebraicSpace S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : T ⟶ Y
  /-- The open `Z ⊂ |T ×_Y X|`. -/
  Z : Opens (Points (pullback a f))
  /-- The restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
  isFinite : IsFinite ((OpenSubspace.ofOpens Z).ι ≫ pullback.fst a f)

namespace Descended

/-- Build a descended 04PC pair from a morphism `a : T ⟶ Y`, an open of
`|T ×_Y X|`, and finiteness of the restricted first projection. -/
def of {T : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (Z : Opens (Points (pullback a f)))
    (h : IsFinite ((OpenSubspace.ofOpens Z).ι ≫ pullback.fst a f)) :
    Descended f T where
  a := a
  Z := Z
  isFinite := h

/-- A descended pair consists of an open of `|T ×_Y X|` whose `ofOpens` subspace
is finite over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (OpenSubspace.ofOpens p.Z).pointsSet = p.Z ∧
      IsFinite ((OpenSubspace.ofOpens p.Z).ι ≫ pullback.fst p.a f) :=
  sorry

/-- The 04PC presentation of a descended pair, taking the open subspace cut out
by the point-set open. -/
def toPair {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    FinitePart f T :=
  FinitePart.of p.a (OpenSubspace.ofOpens p.Z) p.isFinite

/-- `toPair` preserves the morphism to `Y`. -/
theorem toPair_a {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (toPair p).a = p.a :=
  sorry

/-- `toPair` realises the open as `OpenSubspace.ofOpens`. -/
theorem toPair_Z {T : AlgebraicSpace S} {f : X ⟶ Y} (p : Descended f T) :
    (toPair p).Z = OpenSubspace.ofOpens p.Z :=
  sorry

/-- The descended 04PC pair associated to a presheaf morphism `T ⟶ (X/Y)_fin`. -/
def ofHom {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) : Descended f T :=
  of (homToY η) (opensOfHom η) (pairOfHom_isFinite η)

/-- The morphism to `Y` of `ofHom η` is `η` followed by `toY`. -/
theorem ofHom_a {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (ofHom η).a = homToY η :=
  sorry

/-- The open of `ofHom η` is `opensOfHom η`. -/
theorem ofHom_Z {T : AlgebraicSpace S} {f : X ⟶ Y}
    (η : T.functorOfPoints ⟶ finitePart f) :
    (ofHom η).Z = opensOfHom η :=
  sorry

end Descended

/-- Reconstructing a 04PC presentation from `homOfPair p` recovers `p.a` and the
point-set of `p.Z`, but not necessarily the same open-subspace representative. -/
theorem pairOfHom_homOfPair {T : AlgebraicSpace S} {f : X ⟶ Y} (p : FinitePart f T) :
    (pairOfHom (homOfPair p)).a = p.a ∧
      HEq (pairOfHom (homOfPair p)).Z.pointsSet p.Z.pointsSet :=
  sorry

/-- Presheaf morphisms `T ⟶ (X/Y)_fin` are canonically descended 04PC pairs over
`T`. -/
def homEquiv {T : AlgebraicSpace S} (f : X ⟶ Y) :
    (T.functorOfPoints ⟶ finitePart f) ≃ Descended f T where
  toFun := Descended.ofHom
  invFun p := homOfPair p.toPair
  left_inv := sorry
  right_inv := sorry

/-- `homEquiv` sends a presheaf morphism to `Descended.ofHom`. -/
theorem homEquiv_apply {T : AlgebraicSpace S} (f : X ⟶ Y)
    (η : T.functorOfPoints ⟶ finitePart f) :
    homEquiv f η = Descended.ofHom η :=
  sorry

/-- The inverse of `homEquiv` sends a descended pair to `homOfPair` of its
`ofOpens` presentation. -/
theorem homEquiv_symm_apply {T : AlgebraicSpace S} (f : X ⟶ Y)
    (p : Descended f T) :
    (homEquiv f).symm p = homOfPair p.toPair :=
  sorry

end FinitePart

end AlgebraicGeometry.AlgebraicSpace
