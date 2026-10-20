/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct.Bicategory

/-!
# The induced self 2-fibre-product map of a morphism of thickenings

A morphism of thickenings of algebraic stacks induces a thickening of the
chosen self 2-fibre products, and the canonical square of relative diagonals
is a 2-fibre-product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare

variable {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
variable {i : X ⟶ X'} {j : Y ⟶ Y'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The cospan transformation `(f, f) ⟶ (f', f')` with vertex maps `i`, `i`,
and `j`, and generating cells `w.symm`. -/
def selfCospan [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : CospanTransform f f f' f' :=
  CospanTransform.mk i i j w.symm w.symm

/-- The left vertex of `selfCospan w` is `i`. -/
@[simp]
theorem selfCospan_left [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : (selfCospan w).left = i :=
  sorry

/-- The right vertex of `selfCospan w` is `i`. -/
@[simp]
theorem selfCospan_right [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : (selfCospan w).right = i :=
  sorry

/-- The base vertex of `selfCospan w` is `j`. -/
@[simp]
theorem selfCospan_base [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : (selfCospan w).base = j :=
  sorry

/-- The left generating comparison of `selfCospan w` is `w.symm`. -/
@[simp]
theorem selfCospan_leftIso [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (selfCospan w).leftIso = w.symm :=
  sorry

/-- The right generating comparison of `selfCospan w` is `w.symm`. -/
@[simp]
theorem selfCospan_rightIso [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (selfCospan w).rightIso = w.symm :=
  sorry

/-- The induced map `X ×_Y X ⟶ X' ×_{Y'} X'` of chosen self 2-fibre products. -/
def selfMap [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f' f' :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u} (selfCospan w)

/-- `selfMap w` is the two-fibre-product map of `selfCospan w`. -/
@[simp]
theorem selfMap_eq [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    selfMap w = TwoFibreProduct.map.{u + 1, u, u + 1, u} (selfCospan w) :=
  sorry

/-- The induced self 2-fibre-product map of a morphism of thickenings is a
thickening. -/
instance selfMap_isThickening [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : IsThickening (selfMap w) :=
  sorry

section DiagonalComparison

-- The public comparison is assembled from private universal-lift presentations.
-- This scoped module-visibility setting preserves that implementation boundary.
set_option backward.privateInPublic true

namespace Implementation

/-- The cone over `f', f'` with apex `X` and both legs equal to `i`. -/
private abbrev commonCone (i : X ⟶ X') (f' : X' ⟶ Y') : PseudoPullbackCone f' f' where
  pt := X
  fst := i
  snd := i
  iso := Iso.refl (i ≫ f')

/-- First-projection comparison for the composite through the relative diagonal
of `f` and `selfMap w`. -/
private def sourceFst [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w) ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f' ≅ i :=
  let Δ := CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f
  let μ := selfMap w
  let ψ := selfCospan w
  let fst₁ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f
  let fst₂ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f'
  α_ Δ μ fst₂ ≪≫
    whiskerLeftIso Δ (TwoFibreProduct.map.fstIso ψ) ≪≫
    (α_ Δ fst₁ i).symm ≪≫
    whiskerRightIso
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.fstIso.{u + 1, u, u + 1} f) i ≪≫
    λ_ i

/-- Second-projection comparison for the composite through the relative diagonal
of `f` and `selfMap w`. -/
private def sourceSnd [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w) ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f' ≅ i :=
  let Δ := CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f
  let μ := selfMap w
  let ψ := selfCospan w
  let snd₁ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f
  let snd₂ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f'
  α_ Δ μ snd₂ ≪≫
    whiskerLeftIso Δ (TwoFibreProduct.map.sndIso ψ) ≪≫
    (α_ Δ snd₁ i).symm ≪≫
    whiskerRightIso
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.sndIso.{u + 1, u, u + 1} f) i ≪≫
    λ_ i

/-- First-projection comparison for the composite through `i` and the relative
diagonal of `f'`. -/
private def targetFst :
    (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f' ≅ i :=
  let Δ := CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'
  let fst₂ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f'
  α_ i Δ fst₂ ≪≫
    whiskerLeftIso i
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.fstIso.{u + 1, u, u + 1} f') ≪≫
    ρ_ i

/-- Second-projection comparison for the composite through `i` and the relative
diagonal of `f'`. -/
private def targetSnd :
    (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f' ≅ i :=
  let Δ := CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'
  let snd₂ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f'
  α_ i Δ snd₂ ≪≫
    whiskerLeftIso i
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.sndIso.{u + 1, u, u + 1} f') ≪≫
    ρ_ i

/-- Vertexwise presentation of the source composite as `commonCone`. -/
private def sourceApp [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') (k : LocallyDiscrete Limits.WalkingCospan) :
    (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w)).app k ≅
      (commonCone i f').toPseudoCone.π.app k :=
  match k with
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') f').symm ≪≫
      whiskerRightIso (sourceFst w) f'
  | ⟨Limits.WalkingCospan.left⟩ => sourceFst w
  | ⟨Limits.WalkingCospan.right⟩ => sourceSnd w

/-- Walking-cospan naturality of `sourceApp`. -/
private theorem sourceNaturality [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (η : a ⟶ b),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) X).map η ◁
          (sourceApp w b).hom ≫
        ((commonCone i f').toPseudoCone.π.naturality η).hom =
      ((((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
            (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫
              selfMap w)).naturality η).hom ≫
        (sourceApp w a).hom ▷ (Bicategory.cospan f' f').map η :=
  sorry

/-- Invertible modification presenting the source composite as `commonCone`. -/
private def sourcePresentation [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w) ≅
      (commonCone i f').toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (sourceApp w) (sourceNaturality w)

/-- Vertexwise presentation of the target composite as `commonCone`. -/
private def targetApp (i : X ⟶ X') (f' : X' ⟶ Y') (k : LocallyDiscrete Limits.WalkingCospan) :
    (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
        (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f')).app k ≅
      (commonCone i f').toPseudoCone.π.app k :=
  match k with
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f')
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') f').symm ≪≫
      whiskerRightIso targetFst f'
  | ⟨Limits.WalkingCospan.left⟩ => targetFst
  | ⟨Limits.WalkingCospan.right⟩ => targetSnd

/-- Walking-cospan naturality of `targetApp`. -/
private theorem targetNaturality :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (η : a ⟶ b),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) X).map η ◁
          (targetApp i f' b).hom ≫
        ((commonCone i f').toPseudoCone.π.naturality η).hom =
      ((((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
            (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f')).naturality η).hom ≫
        (targetApp i f' a).hom ▷ (Bicategory.cospan f' f').map η :=
  sorry

/-- Invertible modification presenting the target composite as `commonCone`. -/
private def targetPresentation :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f').toPseudoCone.comparison X).obj
        (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') ≅
      (commonCone i f').toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (targetApp i f') targetNaturality

/-- The source composite is the universal lift of `commonCone`. -/
private def sourceUnique [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w ≅
      PseudoPullbackCone.lift (commonCone i f')
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f') :=
  PseudoPullbackCone.lift.uniqueIso (commonCone i f')
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f')
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w)
    (sourcePresentation w)

/-- The target composite is the universal lift of `commonCone`. -/
private def targetUnique :
    i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f' ≅
      PseudoPullbackCone.lift (commonCone i f')
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f') :=
  CategoryTheory.Bicategory.PseudoPullbackCone.lift.uniqueIso (commonCone i f')
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f' f')
    (i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f')
    targetPresentation

end Implementation

/-- The canonical 2-cell filling the diagonal square of a morphism of
thickenings. -/
def diagonalIso [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f ≫ selfMap w ≅
      i ≫ CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f' :=
  Implementation.sourceUnique w ≪≫ Implementation.targetUnique.symm

end DiagonalComparison

/-- The canonical square with apex `X`, top the relative diagonal of `f`, left
`i`, bottom the relative diagonal of `f'`, and right `selfMap w`. -/
def diagonalCone [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    PseudoPullbackCone (selfMap w)
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') where
  pt := X
  fst := CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f
  snd := i
  iso := diagonalIso w

/-- The apex of `diagonalCone w` is `X`. -/
@[simp]
theorem diagonalCone_pt [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : (diagonalCone w).pt = X :=
  sorry

/-- The first leg of `diagonalCone w` is the relative diagonal of `f`. -/
@[simp]
theorem diagonalCone_fst [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (diagonalCone w).fst =
      CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f :=
  sorry

/-- The second leg of `diagonalCone w` is `i`. -/
@[simp]
theorem diagonalCone_snd [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') : (diagonalCone w).snd = i :=
  sorry

/-- The comparison cell of `diagonalCone w` is `diagonalIso w`. -/
@[simp]
theorem diagonalCone_iso [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (diagonalCone w).iso = diagonalIso w :=
  sorry

/-- The canonical square of relative diagonals of a morphism of thickenings is a
2-fibre-product square. -/
instance diagonalCone.isBilimit [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [IsThickening i] [IsThickening j] (w : f ≫ j ≅ i ≫ f') :
    (diagonalCone w).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare

namespace AlgebraicGeometry.AlgebraicStack.IsThickening.Hom

variable {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
variable {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The pair of relative diagonals of a morphism of thickenings is itself a
morphism of thickenings. -/
def diagonalHom (h : Hom i j f f') :
    Hom i (diagonalSquare.selfMap h.w)
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f)
      (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  mk i (diagonalSquare.selfMap h.w)
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f)
    (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f')
    (diagonalSquare.diagonalIso h.w)

/-- The square 2-isomorphism of `diagonalHom h` is `diagonalSquare.diagonalIso h.w`. -/
theorem diagonalHom_w (h : Hom i j f f') :
    (diagonalHom h).w = diagonalSquare.diagonalIso h.w :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
