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
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# The diagonal square of a monomorphism of algebraic stacks

For morphisms of algebraic stacks `X ⟶ X' ⟶ Y`, if `X ⟶ X'` is a
monomorphism then the canonical square of relative diagonals over the
induced map of self 2-fibre products is a 2-fibre-product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Mono

namespace diagonalSquare

variable {S : Scheme.{u}} {X X' Y : GroupoidsOver S}

/-- The cospan transformation `(f ≫ g, f ≫ g) ⟶ (g, g)` with vertex maps
`f`, `f`, and `𝟙 Y`. -/
def cospan (f : X ⟶ X') (g : X' ⟶ Y) :
    CospanTransform (f ≫ g) (f ≫ g) g g :=
  CospanTransform.mk f f (𝟙 Y) (ρ_ (f ≫ g)).symm (ρ_ (f ≫ g)).symm

/-- The left vertex of `cospan f g` is `f`. -/
@[simp]
theorem cospan_left (f : X ⟶ X') (g : X' ⟶ Y) :
    (cospan f g).left = f :=
  rfl

/-- The right vertex of `cospan f g` is `f`. -/
@[simp]
theorem cospan_right (f : X ⟶ X') (g : X' ⟶ Y) :
    (cospan f g).right = f :=
  rfl

/-- The base vertex of `cospan f g` is `𝟙 Y`. -/
@[simp]
theorem cospan_base (f : X ⟶ X') (g : X' ⟶ Y) :
    (cospan f g).base = 𝟙 Y :=
  rfl

/-- The induced map `X ×_Y X ⟶ X' ×_Y X'` of chosen self 2-fibre products. -/
def map (f : X ⟶ X') (g : X' ⟶ Y) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (f ≫ g) (f ≫ g) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} g g :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u} (cospan f g)

/-- `map f g` is the two-fibre-product map of `cospan f g`. -/
@[simp]
theorem map_eq (f : X ⟶ X') (g : X' ⟶ Y) :
    map f g = TwoFibreProduct.map.{u + 1, u, u + 1, u} (cospan f g) :=
  rfl

/-- The cone over `g, g` with apex `X` and both legs equal to `f`. -/
def commonCone (f : X ⟶ X') (g : X' ⟶ Y) : PseudoPullbackCone g g where
  pt := X
  fst := f
  snd := f
  iso := Iso.refl (f ≫ g)

/-- First-projection comparison for the composite through the relative diagonal of
`f ≫ g` and `map f g`. -/
def sourceFst (f : X ⟶ X') (g : X' ⟶ Y) :
    (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g) ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g ≅ f :=
  let Δ := Hom.diagonal.{u + 1, u, u + 1} (f ≫ g)
  let μ := map f g
  let ψ := cospan f g
  let fst₁ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} (f ≫ g) (f ≫ g)
  let fst₂ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g
  α_ Δ μ fst₂ ≪≫
    whiskerLeftIso Δ (TwoFibreProduct.map.fstIso ψ) ≪≫
    (α_ Δ fst₁ ψ.left).symm ≪≫
    whiskerRightIso (Hom.diagonal.fstIso.{u + 1, u, u + 1} (f ≫ g)) ψ.left ≪≫
    λ_ ψ.left ≪≫
    eqToIso (CospanTransform.mk_left f f (𝟙 Y) (ρ_ (f ≫ g)).symm (ρ_ (f ≫ g)).symm)

/-- Second-projection comparison for the composite through the relative diagonal of
`f ≫ g` and `map f g`. -/
def sourceSnd (f : X ⟶ X') (g : X' ⟶ Y) :
    (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g) ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} g g ≅ f :=
  let Δ := Hom.diagonal.{u + 1, u, u + 1} (f ≫ g)
  let μ := map f g
  let ψ := cospan f g
  let snd₁ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} (f ≫ g) (f ≫ g)
  let snd₂ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} g g
  α_ Δ μ snd₂ ≪≫
    whiskerLeftIso Δ (TwoFibreProduct.map.sndIso ψ) ≪≫
    (α_ Δ snd₁ ψ.right).symm ≪≫
    whiskerRightIso (Hom.diagonal.sndIso.{u + 1, u, u + 1} (f ≫ g)) ψ.right ≪≫
    λ_ ψ.right ≪≫
    eqToIso (CospanTransform.mk_right f f (𝟙 Y) (ρ_ (f ≫ g)).symm (ρ_ (f ≫ g)).symm)

/-- First-projection comparison for the composite through `f` and the relative
diagonal of `g`. -/
def targetFst (f : X ⟶ X') (g : X' ⟶ Y) :
    (f ≫ Hom.diagonal.{u + 1, u, u + 1} g) ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g ≅ f :=
  let Δ := Hom.diagonal.{u + 1, u, u + 1} g
  let fst₂ := TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g
  α_ f Δ fst₂ ≪≫
    whiskerLeftIso f (Hom.diagonal.fstIso.{u + 1, u, u + 1} g) ≪≫ ρ_ f

/-- Second-projection comparison for the composite through `f` and the relative
diagonal of `g`. -/
def targetSnd (f : X ⟶ X') (g : X' ⟶ Y) :
    (f ≫ Hom.diagonal.{u + 1, u, u + 1} g) ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} g g ≅ f :=
  let Δ := Hom.diagonal.{u + 1, u, u + 1} g
  let snd₂ := TwoFibreProduct.snd.{u + 1, u, u + 1, u} g g
  α_ f Δ snd₂ ≪≫
    whiskerLeftIso f (Hom.diagonal.sndIso.{u + 1, u, u + 1} g) ≪≫ ρ_ f

section

-- The public comparisons expose their concrete private vertexwise implementations.
set_option backward.privateInPublic true

/-- Vertexwise presentation of the source composite as `commonCone f g`. -/
private def sourceApp (f : X ⟶ X') (g : X' ⟶ Y) :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g).toPseudoCone.comparison X).obj
          (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g)).app j ≅
        (commonCone f g).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g) g).symm ≪≫
      whiskerRightIso (sourceFst f g) g
  | ⟨Limits.WalkingCospan.left⟩ => sourceFst f g
  | ⟨Limits.WalkingCospan.right⟩ => sourceSnd f g

/-- Invertible modification presenting the source composite as `commonCone f g`. -/
def sourcePresentation (f : X ⟶ X') (g : X' ⟶ Y) :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g).toPseudoCone.comparison X).obj
        (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g) ≅
      (commonCone f g).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (sourceApp f g) (by sorry)

/-- Vertexwise presentation of the target composite as `commonCone f g`. -/
private def targetApp (f : X ⟶ X') (g : X' ⟶ Y) :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g).toPseudoCone.comparison X).obj
          (f ≫ Hom.diagonal.{u + 1, u, u + 1} g)).app j ≅
        (commonCone f g).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ (f ≫ Hom.diagonal.{u + 1, u, u + 1} g)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g g) g).symm ≪≫
      whiskerRightIso (targetFst f g) g
  | ⟨Limits.WalkingCospan.left⟩ => targetFst f g
  | ⟨Limits.WalkingCospan.right⟩ => targetSnd f g

/-- Invertible modification presenting the target composite as `commonCone f g`. -/
def targetPresentation (f : X ⟶ X') (g : X' ⟶ Y) :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g).toPseudoCone.comparison X).obj
        (f ≫ Hom.diagonal.{u + 1, u, u + 1} g) ≅
      (commonCone f g).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (targetApp f g) (by sorry)

end

/-- The source composite is the universal lift of `commonCone f g`. -/
def sourceUnique (f : X ⟶ X') (g : X' ⟶ Y) :
    Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g ≅
      PseudoPullbackCone.lift (commonCone f g)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g) :=
  PseudoPullbackCone.lift.uniqueIso (commonCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g)
    (Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g)
    (sourcePresentation f g)

/-- The target composite is the universal lift of `commonCone f g`. -/
def targetUnique (f : X ⟶ X') (g : X' ⟶ Y) :
    f ≫ Hom.diagonal.{u + 1, u, u + 1} g ≅
      PseudoPullbackCone.lift (commonCone f g)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g) :=
  PseudoPullbackCone.lift.uniqueIso (commonCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} g g)
    (f ≫ Hom.diagonal.{u + 1, u, u + 1} g) (targetPresentation f g)

/-- The canonical 2-cell filling the diagonal square. -/
def iso (f : X ⟶ X') (g : X' ⟶ Y) :
    Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) ≫ map f g ≅
      f ≫ Hom.diagonal.{u + 1, u, u + 1} g :=
  sourceUnique f g ≪≫ (targetUnique f g).symm

/-- The canonical square with apex `X`, top the relative diagonal of `f ≫ g`,
left `f`, bottom the relative diagonal of `g`, and right `map f g`. -/
def cone (f : X ⟶ X') (g : X' ⟶ Y) :
    PseudoPullbackCone (map f g) (Hom.diagonal.{u + 1, u, u + 1} g) where
  pt := X
  fst := Hom.diagonal.{u + 1, u, u + 1} (f ≫ g)
  snd := f
  iso := iso f g

/-- The apex of `cone f g` is `X`. -/
@[simp]
theorem cone_pt (f : X ⟶ X') (g : X' ⟶ Y) : (cone f g).pt = X :=
  rfl

/-- The first leg of `cone f g` is the relative diagonal of `f ≫ g`. -/
@[simp]
theorem cone_fst (f : X ⟶ X') (g : X' ⟶ Y) :
    (cone f g).fst = Hom.diagonal.{u + 1, u, u + 1} (f ≫ g) :=
  rfl

/-- The second leg of `cone f g` is `f`. -/
@[simp]
theorem cone_snd (f : X ⟶ X') (g : X' ⟶ Y) : (cone f g).snd = f :=
  rfl

/-- The comparison cell of `cone f g` is `iso f g`. -/
@[simp]
theorem cone_iso (f : X ⟶ X') (g : X' ⟶ Y) : (cone f g).iso = iso f g :=
  rfl

/-- For morphisms of algebraic stacks `X ⟶ X' ⟶ Y`, if
`X ⟶ X'` is a monomorphism then the canonical diagram of relative diagonals
over `X ×_Y X ⟶ X' ×_Y X'` is a 2-fibre-product square. -/
@[instance]
instance cone.isBilimit [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y]
    (f : X ⟶ X') (g : X' ⟶ Y) [Mono f] : (cone f g).IsBilimit :=
  sorry

end diagonalSquare

end Mono

end AlgebraicGeometry.Groupoids.Hom
