/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Finite-part spaces with a section

A morphism `f : X ⟶ Y` of algebraic spaces together with a section `σ` determines
the functor `(X / Y, σ)_fin` of finite-part pairs whose open contains the graph of
`σ`, and — when `f` is separated and locally of finite type — the representing
algebraic space with its étale morphism to `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The two legs `1_T` and `σ ∘ a` agree over `Y` when `σ` is a section of `f`. -/
private theorem unitSection_condition {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : 𝟙 (ofOver T) ≫ a = (a ≫ σ) ≫ f := by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id]

/-- The graph morphism `(1_T, σ ∘ a) : T ⟶ T ×_Y X`. -/
@[no_expose]
def unitSection {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : ofOver T ⟶ pullback a f :=
  pullback.lift (𝟙 (ofOver T)) (a ≫ σ) (unitSection_condition a f σ hσ)

/-- The first component of the unit section is `1_T`. -/
theorem unitSection_fst {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : unitSection a f σ hσ ≫ pullback.fst a f = 𝟙 (ofOver T) := by
  exact pullback.lift_fst _ _ _

/-- The second component of the unit section is `σ ∘ a`. -/
theorem unitSection_snd {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : unitSection a f σ hσ ≫ pullback.snd a f = a ≫ σ := by
  exact pullback.lift_snd _ _ _

namespace WithSection

/-- A finite-part pair `(a, Z)` over `T` through which the graph of `σ` factors. -/
structure Point (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (T : Over S)
    extends FinitePart.Point f T where
  /-- The graph `(1_T, σ ∘ a)` lands in `Z`. -/
  contains_unit : Set.range (Points.map (unitSection a f σ hσ)) ⊆ Z

/-- Build a with-section pair from a finite-part pair containing the graph of `σ`. -/
@[no_expose]
def Point.of {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : FinitePart.Point f T)
    (h : Set.range (Points.map (unitSection p.a f σ hσ)) ⊆ p.Z) :
    Point f σ hσ T where
  toPoint := p
  contains_unit := h

/-- A with-section pair is a finite-part pair whose open contains the graph of `σ`. -/
theorem Point.spec {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : Point f σ hσ T) :
    IsOpenImmersion (OpenSubspace.fromOpens p.Z).ι ∧ IsFinite p.pr0 := p.toPoint.spec

/-- Base change along `h : T' ⟶ T` preserves the unit-section condition. -/
private theorem Point.restrict_contains_unit {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y}
    {T T' : Over S} (p : Point f σ hσ T) (h : T' ⟶ T) :
    Set.range
        (Points.map (unitSection (ofOverMap h ≫ p.a) f σ hσ)) ⊆
      Opens.comap (fiberPointsMap h f p.a) p.Z := sorry

/-- Base change of a with-section pair along `h : T' ⟶ T`. -/
def Point.restrict {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T T' : Over S}
    (p : Point f σ hσ T) (h : T' ⟶ T) : Point f σ hσ T' where
  toPoint := p.toPoint.restrict h
  contains_unit := by exact Point.restrict_contains_unit p h

private theorem Point.ext_toPoint {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ ≫ f = 𝟙 Y} {T : Over S} {p q : Point f σ hσ T}
    (h : p.toPoint = q.toPoint) : p = q := by
  cases p
  cases q
  cases h
  rfl

private theorem Point.restrict_id {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ ≫ f = 𝟙 Y} {T : Over S} (p : Point f σ hσ T) :
    p.restrict (𝟙 T) = p :=
  Point.ext_toPoint (FinitePart.Point.restrict_id p.toPoint)

private theorem Point.restrict_comp {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ ≫ f = 𝟙 Y} {T T' T'' : Over S} (p : Point f σ hσ T)
    (h : T' ⟶ T) (k : T'' ⟶ T') :
    (p.restrict h).restrict k = p.restrict (k ≫ h) :=
  Point.ext_toPoint (FinitePart.Point.restrict_comp p.toPoint h k)

private theorem pointSmall (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) : Small.{u} (Point f σ hσ T) := by
  apply small_of_injective
    (f := fun p : Point f σ hσ T ↦ (pointsFunctor_obj_equiv f T).symm p.toPoint)
  intro p q h
  have h' : p.toPoint = q.toPoint := (pointsFunctor_obj_equiv f T).symm.injective h
  cases p
  cases q
  cases h'
  rfl

private def pointModel (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) : Type u :=
  @Shrink.{u, u + 1} (Point f σ hσ T) (pointSmall f σ hσ T)

private def pointModelEquiv (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) : Point f σ hσ T ≃ pointModel f σ hσ T :=
  @equivShrink.{u, u + 1} (Point f σ hσ T) (pointSmall f σ hσ T)

end WithSection

private def withSectionMap (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    WithSection.pointModel f σ hσ T.unop ⟶ WithSection.pointModel f σ hσ T'.unop :=
  TypeCat.ofHom fun p ↦ WithSection.pointModelEquiv f σ hσ T'.unop
    (((WithSection.pointModelEquiv f σ hσ T.unop).symm p).restrict h.unop)

private theorem withSectionFunctor_map_id (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) (T : (Over S)ᵒᵖ) :
    withSectionMap f σ hσ (𝟙 T) = 𝟙 (WithSection.pointModel f σ hσ T.unop) := sorry

private theorem withSectionFunctor_map_comp (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) {T T' T'' : (Over S)ᵒᵖ} (h : T ⟶ T') (k : T' ⟶ T'') :
    withSectionMap f σ hσ (h ≫ k) =
      withSectionMap f σ hσ h ≫ withSectionMap f σ hσ k := sorry

/-- The finite-part-with-section presheaf assigns finite open families containing the section. -/
@[no_expose]
def withSectionFunctor (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := WithSection.pointModel f σ hσ T.unop
  map := withSectionMap f σ hσ
  map_id := withSectionFunctor_map_id f σ hσ
  map_comp := withSectionFunctor_map_comp f σ hσ

/-- Values of the with-section functor are equivalent to with-section pairs. -/
@[no_expose]
def withSectionFunctor_obj_equiv (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) :
    (withSectionFunctor f σ hσ).obj (op T) ≃ WithSection.Point f σ hσ T :=
  (WithSection.pointModelEquiv f σ hσ T).symm

private theorem withSectionSpace_isSheaf (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (withSectionFunctor f σ hσ) := sorry

private theorem withSectionSpace_representableDiagonal (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    yoneda.relativelyRepresentable (Limits.diag (withSectionFunctor f σ hσ)) := sorry

private theorem withSectionSpace_atlas (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ withSectionFunctor f σ hσ),
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space `(X / Y, σ)_fin` representing the with-section finite-part functor. -/
def withSectionSpace (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : AlgebraicSpace S :=
  ofFunctor (withSectionFunctor f σ hσ) (by exact withSectionSpace_isSheaf f σ hσ)
    (by exact withSectionSpace_representableDiagonal f σ hσ) (by exact withSectionSpace_atlas f σ hσ)

/-- The functor of points of `withSectionSpace f σ hσ` is the with-section functor. -/
theorem withSectionSpace_functorOfPoints (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionSpace f σ hσ).functorOfPoints = withSectionFunctor f σ hσ := by
  exact ofFunctor_functorOfPoints _ _ _ _

private def withSectionToYApp (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : (Over S)ᵒᵖ) : (withSectionFunctor f σ hσ).obj T ⟶ Y.functorOfPoints.obj T :=
  TypeCat.ofHom fun p ↦ Point.a_elem
    (((withSectionFunctor_obj_equiv f σ hσ T.unop) p).toPoint)

private theorem withSectionToY_naturality (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (withSectionFunctor f σ hσ).map h ≫ withSectionToYApp f σ hσ T' =
      withSectionToYApp f σ hσ T ≫ Y.functorOfPoints.map h := sorry

/-- The structure morphism sends a finite family to its morphism into the base. -/
@[no_expose]
def withSectionToY (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : withSectionSpace f σ hσ ⟶ Y where
  app := withSectionToYApp f σ hσ
  naturality {_ _} h := withSectionToY_naturality f σ hσ h

/-- The morphism `(X / Y, σ)_fin ⟶ Y` is étale. -/
instance etale_withSectionToY (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : Etale (withSectionToY f σ hσ) := sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
