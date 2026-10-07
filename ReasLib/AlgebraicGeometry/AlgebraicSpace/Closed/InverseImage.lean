module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Inverse images of closed subspaces of algebraic spaces

The inverse image of a closed subspace along a morphism of algebraic spaces is
formed by the corresponding fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of a closed subspace along a morphism of algebraic spaces. -/
def inverseImage {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] : AlgebraicSpace S :=
  ReasLibPullback.pullbackOver f i X.isSheaf X.representableDiagonal

/-- The functor of points of an inverse image is the corresponding presheaf fibre product. -/
@[simp]
theorem inverseImage_functorOfPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (inverseImage f i).functorOfPoints =
      Limits.pullback (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
        (i : Z.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The inclusion of an inverse image into the ambient algebraic space. -/
def inverseImageι {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] : inverseImage f i ⟶ Y :=
  ReasLibPullback.pullbackOverFst f i X.isSheaf X.representableDiagonal

/-- The comparison morphism from an inverse image to the closed subspace. -/
def inverseImageTo {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] : inverseImage f i ⟶ Z :=
  ReasLibPullback.pullbackOverSnd f i X.isSheaf X.representableDiagonal

/-- The inverse-image inclusion is the first projection of the presheaf fibre product. -/
theorem inverseImageι_eq_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (inverseImageι f i :
        (inverseImage f i).functorOfPoints ⟶ Y.functorOfPoints) =
      Limits.pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
        (i : Z.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The inverse-image comparison morphism is the second projection of the presheaf fibre product. -/
theorem inverseImageTo_eq_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (inverseImageTo f i :
        (inverseImage f i).functorOfPoints ⟶ Z.functorOfPoints) =
      Limits.pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
        (i : Z.functorOfPoints ⟶ X.functorOfPoints) :=
  rfl

/-- The two projections of an inverse image commute with the maps to the ambient space. -/
theorem inverseImage_condition {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    inverseImageι f i ≫ f = inverseImageTo f i ≫ i := by
  change
    Limits.pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
        (i : Z.functorOfPoints ⟶ X.functorOfPoints) ≫
        (f : Y.functorOfPoints ⟶ X.functorOfPoints) =
      Limits.pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
          (i : Z.functorOfPoints ⟶ X.functorOfPoints) ≫
        (i : Z.functorOfPoints ⟶ X.functorOfPoints)
  exact Limits.pullback.condition

/-- The inverse-image projections exhibit the inverse image as a fibre product. -/
theorem inverseImage_isPullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsPullback (inverseImageι f i) (inverseImageTo f i) f i :=
  ReasLibPullback.isPullback f i

/-- A pullback of a closed immersion is a closed immersion. -/
theorem IsClosedImmersion.of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : Y ⟶ X} {i : Z ⟶ X} {pY : P ⟶ Y} {pZ : P ⟶ Z} [IsClosedImmersion i]
    (h : IsPullback pY pZ f i) : IsClosedImmersion pY :=
  sorry

/-- The projection from an inverse image to the ambient space is a closed immersion. -/
instance instIsClosedImmersion_inverseImageι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsClosedImmersion (inverseImageι f i) :=
  IsClosedImmersion.of_isPullback (inverseImage_isPullback f i)

/-- The inverse image, its projections, and its closed-immersion and pullback properties. -/
theorem inverseImage_spec {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (inverseImage f i).functorOfPoints =
        Limits.pullback (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
          (i : Z.functorOfPoints ⟶ X.functorOfPoints) ∧
      (inverseImageι f i :
          (inverseImage f i).functorOfPoints ⟶ Y.functorOfPoints) =
        Limits.pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) (f : Y.functorOfPoints ⟶ X.functorOfPoints)
          (i : Z.functorOfPoints ⟶ X.functorOfPoints) ∧
      IsClosedImmersion (inverseImageι f i) ∧
      IsPullback (inverseImageι f i) (inverseImageTo f i) f i := by
  exact ⟨inverseImage_functorOfPoints f i, inverseImageι_eq_fst f i,
    inferInstance, inverseImage_isPullback f i⟩

end AlgebraicGeometry.AlgebraicSpace
