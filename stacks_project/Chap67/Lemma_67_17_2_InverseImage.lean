module

public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Inverse images of open subspaces of algebraic spaces

The inverse image of an open subspace `U` of an algebraic space `X` along a
morphism `φ : Y ⟶ X` is the fibre product `U ×_X Y`, viewed as an open
subspace of `Y`. The fibre product is formed in the functor-of-points
category, parallel to the closed inverse image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of an open subspace along a morphism of algebraic spaces,
formed as the functor-of-points fibre product. -/
def openInverseImage {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : AlgebraicSpace S :=
  ofFunctor (pullback (toFunctorOfPoints φ) (toFunctorOfPoints ι)) sorry sorry sorry

/-- The functor of points of `openInverseImage φ ι` is the functor-category
pullback of `φ` and `ι`. -/
@[simp]
theorem openInverseImage_functorOfPoints {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImage φ ι).functorOfPoints =
      pullback (toFunctorOfPoints φ) (toFunctorOfPoints ι) :=
  sorry

/-- The open-subspace inclusion of `openInverseImage φ ι` into `Y`. -/
def openInverseImageι {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : openInverseImage φ ι ⟶ Y :=
  pullback.fst (toFunctorOfPoints φ) (toFunctorOfPoints ι)

/-- The comparison morphism of `openInverseImage φ ι` into `U`. -/
def openInverseImageTo {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι] : openInverseImage φ ι ⟶ U :=
  pullback.snd (toFunctorOfPoints φ) (toFunctorOfPoints ι)

/-- The inclusion `openInverseImageι φ ι` is the first projection of the
functor-of-points pullback. -/
theorem openInverseImageι_eq_fst {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    toFunctorOfPoints (openInverseImageι φ ι) =
      pullback.fst (toFunctorOfPoints φ) (toFunctorOfPoints ι) :=
  sorry

/-- The comparison `openInverseImageTo φ ι` is the second projection of the
functor-of-points pullback. -/
theorem openInverseImageTo_eq_snd {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    toFunctorOfPoints (openInverseImageTo φ ι) =
      pullback.snd (toFunctorOfPoints φ) (toFunctorOfPoints ι) :=
  sorry

/-- The two projections of `openInverseImage φ ι` commute with `φ` and `ι`. -/
theorem openInverseImage_condition {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    openInverseImageι φ ι ≫ φ = openInverseImageTo φ ι ≫ ι :=
  sorry

/-- `openInverseImage φ ι` realises the fibre product of `φ` and `ι`. -/
theorem openInverseImage_isPullback {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι :=
  sorry

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
  sorry

/-- The open inverse image is the functor-of-points pullback of `φ` and `ι`, its
inclusion into `Y` is the first projection, that inclusion is an open immersion,
and the resulting square is a pullback. -/
theorem openInverseImage_spec {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] :
    (openInverseImage φ ι).functorOfPoints =
        pullback (toFunctorOfPoints φ) (toFunctorOfPoints ι) ∧
      toFunctorOfPoints (openInverseImageι φ ι) =
        pullback.fst (toFunctorOfPoints φ) (toFunctorOfPoints ι) ∧
      IsOpenImmersion (openInverseImageι φ ι) ∧
      IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
