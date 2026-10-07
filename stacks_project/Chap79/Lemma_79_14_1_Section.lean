module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap79.«79_12_0_2_FinitePart»

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
theorem unitSection_condition {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : 𝟙 (ofOver T) ≫ a = (a ≫ σ) ≫ f := sorry

/-- The graph morphism `(1_T, σ ∘ a) : T ⟶ T ×_Y X`. -/
def unitSection {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : ofOver T ⟶ pullback a f :=
  pullback.lift (𝟙 (ofOver T)) (a ≫ σ) (unitSection_condition a f σ hσ)

/-- The first component of the unit section is `1_T`. -/
theorem unitSection_fst {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : unitSection a f σ hσ ≫ pullback.fst a f = 𝟙 (ofOver T) := sorry

/-- The second component of the unit section is `σ ∘ a`. -/
theorem unitSection_snd {T : Over S} (a : ofOver T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : unitSection a f σ hσ ≫ pullback.snd a f = a ≫ σ := sorry

namespace WithSection

/-- A finite-part pair `(a, Z)` over `T` through which the graph of `σ` factors. -/
structure Point (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (T : Over S)
    extends FinitePart.Point f T where
  /-- The graph `(1_T, σ ∘ a)` lands in `Z`. -/
  contains_unit : Set.range (Points.map (unitSection a f σ hσ)) ⊆ Z

/-- Build a with-section pair from a finite-part pair containing the graph of `σ`. -/
def Point.of {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : FinitePart.Point f T)
    (h : Set.range (Points.map (unitSection p.a f σ hσ)) ⊆ p.Z) :
    Point f σ hσ T where
  toPoint := p
  contains_unit := h

/-- A with-section pair is a finite-part pair whose open contains the graph of `σ`. -/
theorem Point.spec {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : Point f σ hσ T) :
    IsOpenImmersion (OpenSubspace.ofOpens p.Z).ι ∧ IsFinite p.pr0 := sorry

/-- Base change along `h : T' ⟶ T` preserves the unit-section condition. -/
theorem Point.restrict_contains_unit {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y}
    {T T' : Over S} (p : Point f σ hσ T) (h : T' ⟶ T) :
    Set.range
        (Points.map (unitSection (ofOverMap h ≫ p.a) f σ hσ)) ⊆
      Opens.comap (fiberPointsMap h f p.a) p.Z := sorry

/-- Base change of a with-section pair along `h : T' ⟶ T`. -/
def Point.restrict {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T T' : Over S}
    (p : Point f σ hσ T) (h : T' ⟶ T) : Point f σ hσ T' where
  toPoint := p.toPoint.restrict h
  contains_unit := Point.restrict_contains_unit p h

/-- The type of with-section pairs over a scheme `T` is `u`-small. -/
instance instSmall_point {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S} :
    Small.{u} (Point f σ hσ T) := sorry

end WithSection

/-- The finite-part-with-section functor `(X / Y, σ)_fin : (Over S)ᵒᵖ ⥤ Type u`. -/
def withSectionFunctor (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (WithSection.Point f σ hσ T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (WithSection.Point f σ hσ T'.unop)
        (((equivShrink (WithSection.Point f σ hσ T.unop)).symm p).restrict h.unop)
  map_id := sorry
  map_comp := sorry

/-- Values of the with-section functor are equivalent to with-section pairs. -/
def withSectionFunctor_obj_equiv (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) :
    (withSectionFunctor f σ hσ).obj (op T) ≃ WithSection.Point f σ hσ T :=
  (equivShrink (WithSection.Point f σ hσ T)).symm

/-- The algebraic space `(X / Y, σ)_fin` representing the with-section finite-part functor. -/
def withSectionSpace (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : AlgebraicSpace S :=
  ofFunctor (withSectionFunctor f σ hσ) sorry sorry sorry

/-- The functor of points of `withSectionSpace f σ hσ` is the with-section functor. -/
theorem withSectionSpace_functorOfPoints (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionSpace f σ hσ).functorOfPoints = withSectionFunctor f σ hσ := sorry

/-- The morphism `(X / Y, σ)_fin ⟶ Y` sending a pair `(a, Z)` to `a`. -/
def withSectionToY (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) : withSectionSpace f σ hσ ⟶ Y where
  app T :=
    TypeCat.ofHom fun p ↦
      Point.a_elem
        (((equivShrink (WithSection.Point f σ hσ T.unop)).symm p).toPoint)
  naturality := sorry

/-- The morphism `(X / Y, σ)_fin ⟶ Y` is étale. -/
instance etale_withSectionToY (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : Etale (withSectionToY f σ hσ) := sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
