/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-! # Finite-part pairs as opens of points

Finite-part pairs given by actual opens compare with classes of bundled open subspaces.
Their presheaf takes values in the universe of the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace

noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.FinitePart
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A pair `(a, Z)` over a scheme `T` for a morphism `f : X ⟶ Y`: a morphism
`a : ofOver T ⟶ Y` and an open `Z` of `|T ×_Y X|` whose restricted projection to `T`
is finite. -/
structure Point (f : X ⟶ Y) (T : Over S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : ofOver T ⟶ Y
  /-- The open `Z ⊂ |T ×_Y X|`. -/
  Z : Opens (Points (pullback a f))
  /-- The restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
  isFinite : IsFinite ((OpenSubspace.fromOpens Z).ι ≫ pullback.fst a f)

namespace Point

/-- Build a finite-part pair from a morphism `a : T ⟶ Y`, an open of `|T ×_Y X|`,
and finiteness of the restricted first projection. -/
def of {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (Z : Opens (Points (pullback a f)))
    (h : IsFinite ((OpenSubspace.fromOpens Z).ι ≫ pullback.fst a f)) :
    Point f T where
  a := a
  Z := Z
  isFinite := h

/-- The restricted projection `pr₀|_Z : Z ⟶ T`. -/
def pr0 {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    (OpenSubspace.fromOpens p.Z).X ⟶ ofOver T :=
  (OpenSubspace.fromOpens p.Z).ι ≫ pullback.fst p.a f

/-- A finite-part pair consists of an open immersion into `T ×_Y X` whose restricted
first projection is finite. -/
theorem spec {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    IsOpenImmersion (OpenSubspace.fromOpens p.Z).ι ∧ IsFinite p.pr0 :=
  ⟨(OpenSubspace.fromOpens p.Z).isOpenImmersion, p.isFinite⟩

/-- The functor-of-points element of `Y` determined by the morphism `a`. -/
def a_elem {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    Y.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ Y.functorOfPoints)

end Point

/-- The continuous map on points induced by `h × id_X`. -/
def fiberPointsMap {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    C(Points (pullback (ofOverMap h ≫ a) f), Points (pullback a f)) :=
  ⟨Points.map (baseChange h f a), Points.continuous_map (baseChange h f a)⟩

/-- Base change along `h : T' ⟶ T` preserves finiteness of `pr₀|_Z`. -/
theorem Point.restrict_isFinite {f : X ⟶ Y} {T T' : Over S} (p : Point f T) (h : T' ⟶ T) :
    IsFinite
      ((OpenSubspace.fromOpens (Opens.comap (fiberPointsMap h f p.a) p.Z)).ι ≫
        pullback.fst (ofOverMap h ≫ p.a) f) := sorry

namespace Point

/-- Base change of a pair `(a, Z)` along `h : T' ⟶ T`, sending `a` to `a ∘ h` and
`Z` to the inverse image `(h × id_X)⁻¹(Z) = T' ×_T Z`. -/
def restrict {f : X ⟶ Y} {T T' : Over S} (p : Point f T) (h : T' ⟶ T) :
    Point f T' where
  a := ofOverMap h ≫ p.a
  Z := Opens.comap (fiberPointsMap h f p.a) p.Z
  isFinite := Point.restrict_isFinite p h

end Point

/-- A points-open pair determines a bundled open-subspace representative. -/
def Point.toSubspacePoint {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    SubspacePoint f T :=
  SubspacePoint.of p.a (OpenSubspace.fromOpens p.Z) p.isFinite

/-- Replacing a bundled open by its open set of points preserves finiteness. -/
theorem SubspacePoint.toPoint_isFinite {f : X ⟶ Y} {T : Over S}
    (p : SubspacePoint f T) :
    IsFinite ((OpenSubspace.fromOpens p.Z.pointsOpens).ι ≫ pullback.fst p.a f) := by
  sorry

/-- A bundled representative determines its actual open set of points. -/
def SubspacePoint.toPoint {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) :
    Point f T :=
  Point.of p.a p.Z.pointsOpens p.toPoint_isFinite

/-- Equivalent bundled representatives give equal points-open pairs. -/
theorem SubspacePoint.toPoint_rel {f : X ⟶ Y} {T : Over S}
    {p q : SubspacePoint f T} (h : SubspacePoint.Rel f T p q) :
    p.toPoint = q.toPoint := by
  sorry

/-- Constructing the open subspace of an open and taking its points recovers the pair. -/
theorem Point.toSubspacePoint_toPoint {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.toSubspacePoint.toPoint = p := by
  sorry

/-- A bundled open and the reconstruction from its points are equivalent over the fibre. -/
theorem SubspacePoint.toPoint_toSubspacePoint_rel {f : X ⟶ Y} {T : Over S}
    (p : SubspacePoint f T) :
    SubspacePoint.Rel f T p.toPoint.toSubspacePoint p := by
  sorry

/-- The actual points-open pair of a class of bundled representatives. -/
def PointQuot.toPoint {f : X ⟶ Y} {T : Over S} (p : PointQuot f T) : Point f T :=
  Quot.lift SubspacePoint.toPoint (fun _ _ h ↦ SubspacePoint.toPoint_rel h) p

/-- Classes of bundled representatives are equivalent to actual points-open pairs. -/
def pointQuotEquivPoint (f : X ⟶ Y) (T : Over S) : PointQuot f T ≃ Point f T where
  toFun := PointQuot.toPoint
  invFun p := PointQuot.mk p.toSubspacePoint
  left_inv p := by
    induction p using Quot.inductionOn with | h p =>
      exact PointQuot.sound p.toPoint_toSubspacePoint_rel
  right_inv := Point.toSubspacePoint_toPoint

/-- Taking points of a bundled class commutes with inverse image. -/
theorem PointQuot.toPoint_restrict {f : X ⟶ Y} {T T' : Over S}
    (p : PointQuot f T) (h : T' ⟶ T) :
    (p.restrict h).toPoint = p.toPoint.restrict h := by
  sorry

/-- Inverse image along the identity preserves a points-open pair. -/
theorem Point.restrict_id {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.restrict (𝟙 T) = p := by
  sorry

/-- Inverse image of points-open pairs respects composition. -/
theorem Point.restrict_comp {f : X ⟶ Y} {T T' T'' : Over S}
    (p : Point f T) (h : T' ⟶ T) (k : T'' ⟶ T') :
    (p.restrict h).restrict k = p.restrict (k ≫ h) := by
  sorry

private theorem pointSmall (f : X ⟶ Y) (T : Over S) : Small.{u} (Point f T) :=
  small_map (pointQuotEquivPoint f T).symm

private def pointModel (f : X ⟶ Y) (T : Over S) : Type u :=
  @Shrink.{u, u + 1} (Point f T) (pointSmall f T)

private def pointModelEquiv (f : X ⟶ Y) (T : Over S) : Point f T ≃ pointModel f T :=
  @equivShrink.{u, u + 1} (Point f T) (pointSmall f T)

/-- The finite-part presheaf with inverse image of actual points-open pairs. -/
@[no_expose]
def pointsFunctor (f : X ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := pointModel f T.unop
  map {T T'} h := TypeCat.ofHom fun p ↦
    pointModelEquiv f T'.unop (((pointModelEquiv f T.unop).symm p).restrict h.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    change pointModelEquiv f T.unop
      (((pointModelEquiv f T.unop).symm p).restrict (𝟙 T.unop)) = p
    rw [Point.restrict_id, Equiv.apply_symm_apply]
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro p
    change pointModelEquiv _ _ (((pointModelEquiv _ _).symm p).restrict
      (k.unop ≫ h.unop)) = pointModelEquiv _ _
      (((pointModelEquiv _ _).symm (pointModelEquiv _ _
        (((pointModelEquiv _ _).symm p).restrict h.unop))).restrict k.unop)
    rw [Equiv.symm_apply_apply, Point.restrict_comp]

/-- Values of the points-open finite-part presheaf are equivalent to actual pairs. -/
@[no_expose]
def pointsFunctor_obj_equiv (f : X ⟶ Y) (T : Over S) :
    (pointsFunctor f).obj (op T) ≃ Point f T :=
  (pointModelEquiv f T).symm

end AlgebraicGeometry.AlgebraicSpace.FinitePart

namespace AlgebraicGeometry.AlgebraicSpace

/-- The finite-part presheaf of a morphism assigns the opens of each fibre product
whose projection to the test scheme is finite. -/
abbrev finitePart {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Over S)ᵒᵖ ⥤ Type u :=
  FinitePart.pointsFunctor f

/-- The value of the finite-part presheaf is equivalent to pairs of a test morphism
and a points-open in its fibre product with finite first projection. -/
def finitePart_obj_equiv {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Over S) : (finitePart f).obj (op T) ≃ FinitePart.Point f T :=
  FinitePart.pointsFunctor_obj_equiv f T

end AlgebraicGeometry.AlgebraicSpace
