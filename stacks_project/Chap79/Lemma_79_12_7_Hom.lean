module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Structure morphism of the finite-part functor

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` determines the
Type `u` functor `(X/Y)_fin` and the structure morphism `(X/Y)_fin ⟶ Y`,
together with its relative and absolute diagonals.

An open of `|T ×_Y X|` is an open subspace modulo isomorphism over the fibre
product, so sections of `(X/Y)_fin` compare as subspaces rather than as chosen
representatives.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A pair `(a, Z)` over a scheme `T` for a morphism `f : X ⟶ Y`: a morphism
`a : ofOver T ⟶ Y` and an open subspace `Z` of `T ×_Y X` whose restricted
projection to `T` is finite. -/
structure Point (f : X ⟶ Y) (T : Over S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : ofOver T ⟶ Y
  /-- The open subspace `Z ⊂ T ×_Y X`. -/
  Z : OpenSubspace (pullback a f)
  /-- The restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
  isFinite : IsFinite (Z.ι ≫ pullback.fst a f)

/-- Build a finite-part pair from a morphism `a : T ⟶ Y`, an open subspace of
`T ×_Y X`, and finiteness of the restricted first projection. -/
def Point.of {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (Z : OpenSubspace (pullback a f))
    (h : IsFinite (Z.ι ≫ pullback.fst a f)) : Point f T where
  a := a
  Z := Z
  isFinite := h

/-- A finite-part pair is an open immersion into `T ×_Y X` whose restricted
first projection is finite. -/
theorem Point.spec {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    IsOpenImmersion p.Z.ι ∧ IsFinite (p.Z.ι ≫ pullback.fst p.a f) :=
  sorry

/-- The functor-of-points element of `Y` determined by the morphism `a`. -/
def Point.a_elem {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    Y.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ Y.functorOfPoints)

/-- Two finite-part pairs determine the same open of `|T ×_Y X|` when they share
the morphism `a` and their open subspaces are isomorphic over the fibre product. -/
def Point.Rel (f : X ⟶ Y) (T : Over S) (p q : Point f T) : Prop :=
  ∃ (ha : p.a = q.a) (e : p.Z.X ≅ q.Z.X), e.hom ≫ q.Z.ι = ha ▸ p.Z.ι

/-- Finite-part pairs modulo subspace equivalence. -/
def PointQuot (f : X ⟶ Y) (T : Over S) : Type (u + 1) :=
  Quot (Point.Rel f T)

/-- The subspace class of a finite-part pair. -/
def PointQuot.mk {f : X ⟶ Y} {T : Over S} (p : Point f T) : PointQuot f T :=
  Quot.mk (Point.Rel f T) p

/-- Section equality of finite-part pairs is subspace equivalence. -/
theorem PointQuot.sound {f : X ⟶ Y} {T : Over S} {p q : Point f T}
    (h : Point.Rel f T p q) : PointQuot.mk p = PointQuot.mk q :=
  sorry

/-- Subspace classes of pairs agree if and only if the pairs are subspace
equivalent. -/
theorem PointQuot.mk_eq_iff {f : X ⟶ Y} {T : Over S} {p q : Point f T} :
    PointQuot.mk p = PointQuot.mk q ↔ Point.Rel f T p q :=
  sorry

/-- Subspace-equivalent pairs determine the same `Y`-section. -/
theorem Point.a_elem_rel {f : X ⟶ Y} {T : Over S} {p q : Point f T}
    (h : Point.Rel f T p q) : p.a_elem = q.a_elem :=
  sorry

/-- The `Y`-section of a subspace class of finite-part pairs. -/
def PointQuot.a_elem {f : X ⟶ Y} {T : Over S} (p : PointQuot f T) :
    Y.functorOfPoints.obj (op T) :=
  Quot.lift Point.a_elem (fun _ _ h ↦ Point.a_elem_rel h) p

/-- The `Y`-section of a subspace class recovers `Point.a_elem`. -/
theorem PointQuot.a_elem_mk {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    (PointQuot.mk p).a_elem = p.a_elem :=
  sorry

/-- The maps `pr₀ ≫ ofOverMap h` and `pr₁` out of `T' ×_Y X` agree over `Y`. -/
theorem baseChange_condition {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y)
    (a : ofOver T ⟶ Y) :
    (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h) ≫ a =
      pullback.snd (ofOverMap h ≫ a) f ≫ f :=
  sorry

/-- The comparison `h × id_X : T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T`. -/
def baseChange {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    pullback (ofOverMap h ≫ a) f ⟶ pullback a f :=
  pullback.lift (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h)
    (pullback.snd (ofOverMap h ≫ a) f) (baseChange_condition h f a)

/-- The inverse-image inclusion of an open subspace along `h × id_X` is an
open immersion. -/
theorem isOpenImmersion_restrictι {f : X ⟶ Y} {T T' : Over S}
    (p : Point f T) (h : T' ⟶ T) :
    AlgebraicSpace.IsOpenImmersion (pullback.fst (baseChange h f p.a) p.Z.ι) :=
  sorry

/-- Base change along `h : T' ⟶ T` preserves finiteness of `pr₀|_Z`. -/
theorem restrict_isFinite {f : X ⟶ Y} {T T' : Over S} (p : Point f T)
    (h : T' ⟶ T) :
    IsFinite
      (pullback.fst (baseChange h f p.a) p.Z.ι ≫
        pullback.fst (ofOverMap h ≫ p.a) f) :=
  sorry

/-- Base change of a pair `(a, Z)` along `h : T' ⟶ T`, sending `a` to `a ∘ h`
and `Z` to the inverse image `(h × id_X)⁻¹(Z) = T' ×_T Z`. -/
def Point.restrict {f : X ⟶ Y} {T T' : Over S} (p : Point f T) (h : T' ⟶ T) :
    Point f T' :=
  Point.of (ofOverMap h ≫ p.a)
    { X := pullback (baseChange h f p.a) p.Z.ι
      ι := pullback.fst (baseChange h f p.a) p.Z.ι
      isOpenImmersion := isOpenImmersion_restrictι p h }
    (restrict_isFinite p h)

/-- Inverse image preserves subspace equivalence of finite-part pairs. -/
theorem Point.Rel.restrict {f : X ⟶ Y} {T T' : Over S} (h : T' ⟶ T)
    {p q : Point f T} (hpq : Point.Rel f T p q) :
    Point.Rel f T' (p.restrict h) (q.restrict h) :=
  sorry

/-- Base change of a subspace class along `h : T' ⟶ T`. -/
def PointQuot.restrict {f : X ⟶ Y} {T T' : Over S} (p : PointQuot f T)
    (h : T' ⟶ T) : PointQuot f T' :=
  Quot.lift (fun p : Point f T ↦ PointQuot.mk (p.restrict h))
    (fun _ _ hpq ↦ PointQuot.sound (Point.Rel.restrict h hpq)) p

/-- Inverse image of a subspace class recovers the class of the inverse image. -/
theorem PointQuot.restrict_mk {f : X ⟶ Y} {T T' : Over S} (p : Point f T)
    (h : T' ⟶ T) : (PointQuot.mk p).restrict h = PointQuot.mk (p.restrict h) :=
  sorry

/-- The type of finite-part pairs over a scheme `T` is `u`-small. -/
instance instSmall_point {f : X ⟶ Y} {T : Over S} : Small.{u} (Point f T) :=
  sorry

/-- The type of subspace classes of finite-part pairs over `T` is `u`-small. -/
instance instSmall_pointQuot {f : X ⟶ Y} {T : Over S} :
    Small.{u} (PointQuot f T) :=
  sorry

/-- The finite-part functor `(X/Y)_fin : (Over S)ᵒᵖ ⥤ Type u`. -/
def functor (f : X ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (PointQuot f T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (PointQuot f T'.unop)
        (((equivShrink (PointQuot f T.unop)).symm p).restrict h.unop)
  map_id := sorry
  map_comp := sorry

/-- Values of the finite-part functor are equivalent to subspace classes of
pairs `(a, Z)`. -/
def functor_obj_equiv (f : X ⟶ Y) (T : Over S) :
    (functor f).obj (op T) ≃ PointQuot f T :=
  (equivShrink (PointQuot f T)).symm

/-- Evaluating the finite-part functor at `T` recovers subspace classes of
pairs over `T`. -/
theorem functor_obj_equiv_apply (f : X ⟶ Y) {T : Over S}
    (p : (functor f).obj (op T)) :
    functor_obj_equiv f T p = (equivShrink (PointQuot f T)).symm p :=
  sorry

/-- The structure morphism `(X/Y)_fin ⟶ Y`, sending a pair `(a, Z)` to the
`Y`-section `a`. -/
def hom (f : X ⟶ Y) : functor f ⟶ Y.functorOfPoints where
  app T := TypeCat.ofHom fun p ↦ (functor_obj_equiv f T.unop p).a_elem
  naturality := sorry

/-- Components of `hom f` recover `PointQuot.a_elem`. -/
theorem hom_app (f : X ⟶ Y) (T : (Over S)ᵒᵖ) (p : (functor f).obj T) :
    (hom f).app T p = (functor_obj_equiv f T.unop p).a_elem :=
  sorry

/-- On a pair `(a, Z)`, the structure morphism records `a` as `Point.a_elem`. -/
theorem hom_spec (f : X ⟶ Y) {T : Over S} (p : Point f T) :
    (hom f).app (op T) ((functor_obj_equiv f T).symm (PointQuot.mk p)) = p.a_elem :=
  sorry

/-- The relative diagonal of `(X/Y)_fin ⟶ Y`. -/
abbrev diagonal (f : X ⟶ Y) : functor f ⟶ pullback (hom f) (hom f) :=
  pullback.diagonal (hom f)

/-- The relative diagonal of `(X/Y)_fin ⟶ Y` is the pullback diagonal of `hom f`. -/
theorem diagonal_eq (f : X ⟶ Y) : diagonal f = pullback.diagonal (hom f) :=
  sorry

/-- The absolute diagonal of `(X/Y)_fin`. -/
abbrev diag (f : X ⟶ Y) : functor f ⟶ functor f ⨯ functor f :=
  Limits.diag (functor f)

/-- The absolute diagonal of `(X/Y)_fin` is the product diagonal of `(X/Y)_fin`. -/
theorem diag_eq (f : X ⟶ Y) : diag f = Limits.diag (functor f) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.FinitePart
