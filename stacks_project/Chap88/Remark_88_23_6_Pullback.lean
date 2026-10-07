module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap87.Lemma_87_14_4_Completion

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
    Closeds (Points (pullbackOver f f X.isSheaf X.representableDiagonal)) :=
  T.preimage (Points.continuous_map (pullbackOverFst f f X.isSheaf X.representableDiagonal ≫ f))

/-- `fibreProductInverseImage f T` is equally the inverse image of `T` along the
second projection of `X' ×_X X'` composed with `f`. -/
theorem fibreProductInverseImage_snd {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    fibreProductInverseImage f T =
      T.preimage
        (Points.continuous_map (pullbackOverSnd f f X.isSheaf X.representableDiagonal ≫ f)) :=
  sorry

/-- A Yoneda section of `X' ×_X X'` maps into `fibreProductInverseImage f T` if and
only if both projections map into the inverse image of `T` on `X'`. -/
theorem mapsInto_fibreProductInverseImage_iff {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) {U : Over S}
    (x : (pullbackOver f f X.isSheaf X.representableDiagonal).functorOfPoints.obj (op U)) :
    mapsInto (fibreProductInverseImage f T : Set
        (Points (pullbackOver f f X.isSheaf X.representableDiagonal))) x ↔
      mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((pullbackOverFst f f X.isSheaf X.representableDiagonal).app (op U) x) ∧
        mapsInto (T.preimage (Points.continuous_map f) : Set (Points X'))
          ((pullbackOverSnd f f X.isSheaf X.representableDiagonal).app (op U) x) :=
  sorry

/-- The first projection `(X' ×_X X')_/T'' ⟶ X'_/T'` of the completed fibre
product. -/
def fibreProductFst {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong (pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun x ↦
    ⟨(pullbackOverFst f f X.isSheaf X.representableDiagonal).app U x.1, sorry⟩
  naturality := sorry

/-- The second projection `(X' ×_X X')_/T'' ⟶ X'_/T'` of the completed fibre
product. -/
def fibreProductSnd {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong (pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun x ↦
    ⟨(pullbackOverSnd f f X.isSheaf X.representableDiagonal).app U x.1, sorry⟩
  naturality := sorry

/-- Components of `fibreProductFst f T` are the first projections of `X' ×_X X'`. -/
theorem fibreProductFst_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong (pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T)).obj U) :
    (ι X' (T.preimage (Points.continuous_map f))).app U ((fibreProductFst f T).app U x) =
      (pullbackOverFst f f X.isSheaf X.representableDiagonal).app U
        ((ι (pullbackOver f f X.isSheaf X.representableDiagonal)
            (fibreProductInverseImage f T)).app U x) :=
  sorry

/-- Components of `fibreProductSnd f T` are the second projections of `X' ×_X X'`. -/
theorem fibreProductSnd_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong (pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T)).obj U) :
    (ι X' (T.preimage (Points.continuous_map f))).app U ((fibreProductSnd f T).app U x) =
      (pullbackOverSnd f f X.isSheaf X.representableDiagonal).app U
        ((ι (pullbackOver f f X.isSheaf X.representableDiagonal)
            (fibreProductInverseImage f T)).app U x) :=
  sorry

/-- The completion of the relative diagonal `Δ_f : X' ⟶ X' ×_X X'` along the
inverse image of `T`. -/
def diagonalMap {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong X' (T.preimage (Points.continuous_map f)) ⟶
      completionAlong (pullbackOver f f X.isSheaf X.representableDiagonal)
        (fibreProductInverseImage f T) where
  app U := ofHom fun x ↦ ⟨(diagonal f).app U x.1, sorry⟩
  naturality := sorry

/-- Components of `diagonalMap f T` are the components of the relative diagonal
of `f`. -/
theorem diagonalMap_app {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong X' (T.preimage (Points.continuous_map f))).obj U) :
    (ι (pullbackOver f f X.isSheaf X.representableDiagonal)
          (fibreProductInverseImage f T)).app U ((diagonalMap f T).app U x) =
      (diagonal f).app U
        ((ι X' (T.preimage (Points.continuous_map f))).app U x) :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
