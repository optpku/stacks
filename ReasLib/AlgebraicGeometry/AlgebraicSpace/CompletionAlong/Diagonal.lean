module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Completions of fibre products along a closed subset

The fibre product of completions of a morphism of algebraic spaces along a
closed subset is identified with the completion of the fibre product, as
subfunctors of that fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- The inverse image of `T` on the fibre product `X' ×_X X'`, taken along the
structure morphism given by either projection to `X`. -/
def fibreProductInverseImage {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    Closeds (Points (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)) :=
  T.preimage (Points.continuous_map (ReasLibPullback.pullbackOverFst f f X.isSheaf X.representableDiagonal ≫ f))

/-- `fibreProductInverseImage f T` is equally the inverse image of `T` along the
second projection of `X' ×_X X'` composed with `f`. -/
theorem fibreProductInverseImage_snd {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    fibreProductInverseImage f T =
      T.preimage
        (Points.continuous_map (ReasLibPullback.pullbackOverSnd f f X.isSheaf X.representableDiagonal ≫ f)) :=
  sorry

/-- A Yoneda section of `X' ×_X X'` maps into `fibreProductInverseImage f T` if and
only if both projections map into the inverse image of `T` on `X'`. -/
theorem mapsInto_fibreProductInverseImage_iff {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) {U : Over S}
    (x : (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal).functorOfPoints.obj (op U)) :
    mapsInto (fibreProductInverseImage f T : Set
        (Points (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal))) x ↔
      mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((ReasLibPullback.pullbackOverFst f f X.isSheaf X.representableDiagonal).app (op U) x) ∧
        mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((ReasLibPullback.pullbackOverSnd f f X.isSheaf X.representableDiagonal).app (op U) x) :=
  sorry

/-- The first projection `(X' ×_X X')_/T'' ⟶ X'_/T'` of the completed fibre
product. -/
def fibreProductFst {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun x ↦
    ⟨(ReasLibPullback.pullbackOverFst f f X.isSheaf X.representableDiagonal).app U x.1,
      ((mapsInto_fibreProductInverseImage_iff f T x.1).mp x.2).1⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k :
        (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal).functorOfPoints.obj U ⟶
          X'.functorOfPoints.obj V ↦ k x.1)
      ((ReasLibPullback.pullbackOverFst f f X.isSheaf X.representableDiagonal).naturality φ)

/-- The second projection `(X' ×_X X')_/T'' ⟶ X'_/T'` of the completed fibre
product. -/
def fibreProductSnd {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun x ↦
    ⟨(ReasLibPullback.pullbackOverSnd f f X.isSheaf X.representableDiagonal).app U x.1,
      ((mapsInto_fibreProductInverseImage_iff f T x.1).mp x.2).2⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k :
        (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal).functorOfPoints.obj U ⟶
          X'.functorOfPoints.obj V ↦ k x.1)
      ((ReasLibPullback.pullbackOverSnd f f X.isSheaf X.representableDiagonal).naturality φ)

/-- Components of `fibreProductFst f T` are the first projections of `X' ×_X X'`. -/
theorem fibreProductFst_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T)).obj U) :
    (ι X' (T.preimage (Points.continuous_map f))).app U ((fibreProductFst f T).app U x) =
      (ReasLibPullback.pullbackOverFst f f X.isSheaf X.representableDiagonal).app U
        ((ι (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
            (fibreProductInverseImage f T)).app U x) :=
  rfl

/-- Components of `fibreProductSnd f T` are the second projections of `X' ×_X X'`. -/
theorem fibreProductSnd_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T)).obj U) :
    (ι X' (T.preimage (Points.continuous_map f))).app U ((fibreProductSnd f T).app U x) =
      (ReasLibPullback.pullbackOverSnd f f X.isSheaf X.representableDiagonal).app U
        ((ι (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
            (fibreProductInverseImage f T)).app U x) :=
  rfl

/-- The completion of the relative diagonal `Δ_f : X' ⟶ X' ×_X X'` along the
inverse image of `T`. -/
def diagonalMap {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong X' (T.preimage (Points.continuous_map f)) ⟶
      completionAlong (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) where
  app U := ofHom fun x ↦
    ⟨(pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u)
      (f : X'.functorOfPoints ⟶ X.functorOfPoints)).app U x.1, by
      apply (mapsInto_fibreProductInverseImage_iff f T _).mpr
      constructor
      · change mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u)
      (f : X'.functorOfPoints ⟶ X.functorOfPoints) ≫
            pullback.fst _ _).app U x.1)
        rw [pullback.diagonal_fst]
        exact x.2
      · change mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u)
      (f : X'.functorOfPoints ⟶ X.functorOfPoints) ≫
            pullback.snd _ _).app U x.1)
        rw [pullback.diagonal_snd]
        exact x.2⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k : X'.functorOfPoints.obj U ⟶
        (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal).functorOfPoints.obj V ↦
          k x.1)
      ((pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u)
      (f : X'.functorOfPoints ⟶ X.functorOfPoints)).naturality φ)

/-- Components of `diagonalMap f T` are the components of the relative diagonal
of `f`. -/
theorem diagonalMap_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong X' (T.preimage (Points.continuous_map f))).obj U) :
    (ι (ReasLibPullback.pullbackOver f f X.isSheaf X.representableDiagonal)
          (fibreProductInverseImage f T)).app U ((diagonalMap f T).app U x) =
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u)
      (f : X'.functorOfPoints ⟶ X.functorOfPoints)).app U
        ((ι X' (T.preimage (Points.continuous_map f))).app U x) :=
  rfl

end completionAlong

/-- The completion of a self-fibre product along the inverse image of a closed subset
is the fibre product of the corresponding completions, with its restricted projections. -/
theorem isPullback_completionAlong_fibreProduct {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    IsPullback (completionAlong.fibreProductFst f T) (completionAlong.fibreProductSnd f T)
      (completionAlong.map f T) (completionAlong.map f T) :=
  sorry

/-- Under the canonical fibre-product comparison, the restriction of the relative diagonal
to the completion equals the relative diagonal of the completed morphism. -/
theorem completionAlong_diagonal {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    completionAlong.diagonalMap f T ≫
        (isPullback_completionAlong_fibreProduct f T).isoPullback.hom =
      pullback.diagonal (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
