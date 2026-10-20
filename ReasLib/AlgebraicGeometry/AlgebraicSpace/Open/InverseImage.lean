module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RepresentableProperties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Open

variable {S : Scheme.{u}} {X Y V : AlgebraicSpace S}

/-- The inverse-image presheaf of an open subspace satisfies fppf descent. -/
theorem inverseImage_isSheaf (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι) :=
  ReasLibPullback.pullbackOver_isSheaf (F := X) (G := V) f ι Y.isSheaf

/-- The inverse-image presheaf of an open subspace has representable diagonal. -/
theorem inverseImage_representableDiagonal (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    yoneda.relativelyRepresentable
      (Limits.diag (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι)) :=
  ReasLibPullback.pullbackOver_representableDiagonal (F := X) (G := V) f ι
    Y.representableDiagonal

/-- The inverse-image presheaf of an open subspace admits a representable étale,
locally-surjective scheme atlas. -/
theorem inverseImage_atlas (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    ∃ (U : Over S) (chart : yoneda.obj U ⟶
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι),
      Representable.Etale chart ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) chart :=
  ReasLibPullback.pullbackOver_hasAtlas (F := X) (G := V) f ι Y.representableDiagonal

/-- The inverse image of an open subspace is the algebraic space whose functor of points is
the presheaf fiber product. -/
def inverseImage (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    AlgebraicSpace S :=
  ofFunctor (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι)
    (inverseImage_isSheaf f ι h_open) (inverseImage_representableDiagonal f ι h_open)
    (inverseImage_atlas f ι h_open)

/-- The inclusion of an inverse-image open subspace is the first presheaf pullback
projection. -/
def inverseImageι (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    inverseImage f ι h_open ⟶ X :=
  pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f ι

/-- The morphism from an inverse-image open subspace to the given open is the second
presheaf pullback projection. -/
def inverseImageTo (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    inverseImage f ι h_open ⟶ V :=
  pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) f ι

/-- The inclusion of the inverse image of an open subspace is a representable open
immersion. -/
theorem inverseImage_isOpenImmersion (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    Representable.IsOpenImmersion (inverseImageι f ι h_open) := by
  exact (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.over
      (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}))).of_isPullback
        (IsPullback.of_hasPullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι).flip h_open

/-- The inverse-image space has the presheaf fiber product as its functor of points, and its
two projections form the corresponding presheaf pullback square. -/
theorem inverseImage_spec (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    (inverseImage f ι h_open).functorOfPoints =
        pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι ∧
      IsPullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (inverseImageι f ι h_open) (inverseImageTo f ι h_open) f ι :=
  ⟨rfl, IsPullback.of_hasPullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι⟩

end AlgebraicGeometry.AlgebraicSpace.Open

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of an open subspace along a morphism of algebraic spaces,
formed as the functor-of-points fibre product. -/
def openInverseImage {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : AlgebraicSpace S :=
  Open.inverseImage φ ι (inferInstance : IsOpenImmersion ι).presheaf

/-- The functor of points of `openInverseImage φ ι` is the functor-category
pullback of `φ` and `ι`. -/
@[simp]
theorem openInverseImage_functorOfPoints {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImage φ ι).functorOfPoints =
      pullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (φ : Y.functorOfPoints ⟶ X.functorOfPoints) (ι : U.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The open-subspace inclusion of `openInverseImage φ ι` into `Y`. -/
def openInverseImageι {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : openInverseImage φ ι ⟶ Y :=
  Open.inverseImageι φ ι (inferInstance : IsOpenImmersion ι).presheaf

/-- The comparison morphism of `openInverseImage φ ι` into `U`. -/
def openInverseImageTo {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : openInverseImage φ ι ⟶ U :=
  Open.inverseImageTo φ ι (inferInstance : IsOpenImmersion ι).presheaf

/-- The inclusion `openInverseImageι φ ι` is the first projection of the
functor-of-points pullback. -/
theorem openInverseImageι_eq_fst {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImageι φ ι : (openInverseImage φ ι).functorOfPoints ⟶ Y.functorOfPoints) =
      pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u)
        (φ : Y.functorOfPoints ⟶ X.functorOfPoints) (ι : U.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The comparison `openInverseImageTo φ ι` is the second projection of the
functor-of-points pullback. -/
theorem openInverseImageTo_eq_snd {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImageTo φ ι : (openInverseImage φ ι).functorOfPoints ⟶ U.functorOfPoints) =
      pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u)
        (φ : Y.functorOfPoints ⟶ X.functorOfPoints) (ι : U.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The two projections of `openInverseImage φ ι` commute with `φ` and `ι`. -/
theorem openInverseImage_condition {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    openInverseImageι φ ι ≫ φ = openInverseImageTo φ ι ≫ ι :=
  Limits.pullback.condition (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (φ : Y.functorOfPoints ⟶ X.functorOfPoints))
    (g := (ι : U.functorOfPoints ⟶ X.functorOfPoints))

/-- `openInverseImage φ ι` realises the fibre product of `φ` and `ι`. -/
theorem openInverseImage_isPullback {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι :=
  ReasLibPullback.isPullback φ ι

/-- A morphism over a common target induces a comparison between the inverse
images of an open subspace of that target. -/
def openInverseImageMap {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImage f ι ⟶ openInverseImage g ι :=
  (openInverseImage_isPullback g ι).lift (openInverseImageι f ι ≫ h)
    (openInverseImageTo f ι) (by
      rw [Category.assoc, w]
      exact openInverseImage_condition f ι)

/-- The comparison of open inverse images commutes with their inclusions. -/
theorem openInverseImageMap_ι {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImageMap f g h ι w ≫ openInverseImageι g ι =
      openInverseImageι f ι ≫ h := by
  unfold openInverseImageMap
  exact (openInverseImage_isPullback g ι).lift_fst (openInverseImageι f ι ≫ h)
    (openInverseImageTo f ι) (by
      rw [Category.assoc, w]
      exact openInverseImage_condition f ι)

/-- The comparison of open inverse images commutes with their morphisms to
the given open subspace. -/
theorem openInverseImageMap_to {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImageMap f g h ι w ≫ openInverseImageTo g ι =
      openInverseImageTo f ι := by
  unfold openInverseImageMap
  exact (openInverseImage_isPullback g ι).lift_snd (openInverseImageι f ι ≫ h)
    (openInverseImageTo f ι) (by
      rw [Category.assoc, w]
      exact openInverseImage_condition f ι)

/-- A morphism into `Y` that realises a fibre product with an open immersion into
`X` is an open immersion. -/
theorem IsOpenImmersion.of_isPullback {S : Scheme.{u}} {X Y U P : AlgebraicSpace S}
    {f : Y ⟶ X} {ι : U ⟶ X} {pY : P ⟶ Y} {pU : P ⟶ U} [IsOpenImmersion ι]
    (h : IsPullback pY pU f ι) : IsOpenImmersion pY :=
  sorry

/-- The inverse-image projection `openInverseImageι φ ι` is an open immersion. -/
instance instIsOpenImmersion_openInverseImageι {S : Scheme.{u}}
    {X Y U : AlgebraicSpace S} (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsOpenImmersion (openInverseImageι φ ι) :=
  ⟨Open.inverseImage_isOpenImmersion φ ι (inferInstance : IsOpenImmersion ι).presheaf⟩

/-- The open inverse image is the functor-of-points pullback of `φ` and `ι`, its
inclusion into `Y` is the first projection, that inclusion is an open immersion,
and the resulting square is a pullback. -/
theorem openInverseImage_spec {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImage φ ι).functorOfPoints =
        pullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (φ : Y.functorOfPoints ⟶ X.functorOfPoints) (ι : U.functorOfPoints ⟶ X.functorOfPoints) ∧
      (openInverseImageι φ ι : (openInverseImage φ ι).functorOfPoints ⟶ Y.functorOfPoints) =
        pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u)
        (φ : Y.functorOfPoints ⟶ X.functorOfPoints) (ι : U.functorOfPoints ⟶ X.functorOfPoints) ∧
      IsOpenImmersion (openInverseImageι φ ι) ∧
      IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι :=
  ⟨openInverseImage_functorOfPoints φ ι, openInverseImageι_eq_fst φ ι,
    inferInstance, openInverseImage_isPullback φ ι⟩

end AlgebraicGeometry.AlgebraicSpace
