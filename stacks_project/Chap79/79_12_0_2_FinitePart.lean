module

public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-!
# Finite-part functor of a morphism of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` determines a functor
`(X/Y)_fin : (Over S)ᵒᵖ ⥤ Type u` whose value at a scheme `T` over `S` is the type of
pairs `(a, Z)` with `a : ofOver T ⟶ Y` and `Z` an open of `|T ×_Y X|` such that
`pr₀|_Z` is finite.
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
  isFinite : IsFinite ((OpenSubspace.ofOpens Z).ι ≫ pullback.fst a f)

namespace Point

/-- Build a finite-part pair from a morphism `a : T ⟶ Y`, an open of `|T ×_Y X|`,
and finiteness of the restricted first projection. -/
def of {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (Z : Opens (Points (pullback a f)))
    (h : IsFinite ((OpenSubspace.ofOpens Z).ι ≫ pullback.fst a f)) :
    Point f T where
  a := a
  Z := Z
  isFinite := h

/-- The restricted projection `pr₀|_Z : Z ⟶ T`. -/
def pr0 {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    (OpenSubspace.ofOpens p.Z).X ⟶ ofOver T :=
  (OpenSubspace.ofOpens p.Z).ι ≫ pullback.fst p.a f

/-- A finite-part pair consists of an open immersion into `T ×_Y X` whose restricted
first projection is finite. -/
theorem spec {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    IsOpenImmersion (OpenSubspace.ofOpens p.Z).ι ∧ IsFinite p.pr0 := sorry

/-- The functor-of-points element of `Y` determined by the morphism `a`. -/
def a_elem {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    Y.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ Y.functorOfPoints)

end Point

/-- The maps `pr₀ ≫ ofOverMap h` and `pr₁` out of `T' ×_Y X` agree over `Y`, so they
induce `h × id_X : T' ×_Y X ⟶ T ×_Y X`. -/
theorem baseChange_condition {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y)
    (a : ofOver T ⟶ Y) :
    (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h) ≫ a =
      pullback.snd (ofOverMap h ≫ a) f ≫ f := sorry

/-- The comparison `h × id_X : T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T`. -/
def baseChange {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    pullback (ofOverMap h ≫ a) f ⟶ pullback a f :=
  pullback.lift (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h)
    (pullback.snd (ofOverMap h ≫ a) f) (baseChange_condition h f a)

/-- The comparison `baseChange h f a` commutes with the first projections via `ofOverMap h`. -/
theorem baseChange_fst {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    baseChange h f a ≫ pullback.fst a f =
      pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h := sorry

/-- The comparison `baseChange h f a` commutes with the second projections. -/
theorem baseChange_snd {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    baseChange h f a ≫ pullback.snd a f = pullback.snd (ofOverMap h ≫ a) f := sorry

/-- The continuous map on points induced by `h × id_X`. -/
def fiberPointsMap {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    C(Points (pullback (ofOverMap h ≫ a) f), Points (pullback a f)) :=
  ⟨Points.map (baseChange h f a), Points.continuous_map (baseChange h f a)⟩

/-- Base change along `h : T' ⟶ T` preserves finiteness of `pr₀|_Z`. -/
theorem restrict_isFinite {f : X ⟶ Y} {T T' : Over S} (p : Point f T) (h : T' ⟶ T) :
    IsFinite
      ((OpenSubspace.ofOpens (Opens.comap (fiberPointsMap h f p.a) p.Z)).ι ≫
        pullback.fst (ofOverMap h ≫ p.a) f) := sorry

namespace Point

/-- Base change of a pair `(a, Z)` along `h : T' ⟶ T`, sending `a` to `a ∘ h` and
`Z` to the inverse image `(h × id_X)⁻¹(Z) = T' ×_T Z`. -/
def restrict {f : X ⟶ Y} {T T' : Over S} (p : Point f T) (h : T' ⟶ T) :
    Point f T' where
  a := ofOverMap h ≫ p.a
  Z := Opens.comap (fiberPointsMap h f p.a) p.Z
  isFinite := restrict_isFinite p h

end Point

/-- The type of finite-part pairs over a scheme `T` is `u`-small. -/
instance instSmall_point {f : X ⟶ Y} {T : Over S} : Small.{u} (Point f T) := sorry

/-- The finite-part functor `(X/Y)_fin : (Over S)ᵒᵖ ⥤ Type u`. -/
def functor (f : X ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (Point f T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (Point f T'.unop)
        (((equivShrink (Point f T.unop)).symm p).restrict h.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the finite-part functor at `T` gives the shrunk type of pairs over `T`. -/
theorem functor_obj (f : X ⟶ Y) (T : Over S) :
    (functor f).obj (op T) = Shrink (Point f T) := sorry

/-- The finite-part functor acts on a morphism by inverse image of pairs. -/
theorem functor_map (f : X ⟶ Y) {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (functor f).map h =
      TypeCat.ofHom fun p ↦
        equivShrink (Point f T'.unop)
          (((equivShrink (Point f T.unop)).symm p).restrict h.unop) := sorry

/-- Values of the finite-part functor are equivalent to pairs `(a, Z)`. -/
def functor_obj_equiv (f : X ⟶ Y) (T : Over S) :
    (functor f).obj (op T) ≃ Point f T :=
  (equivShrink (Point f T)).symm

end AlgebraicGeometry.AlgebraicSpace.FinitePart
