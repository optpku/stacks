/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Automorphisms
public import ReasLib.AlgebraicGeometry.GroupoidsOver.BaseProjection

/-!
# Relative isomorphism sheaves

For morphisms `x1, x2 : Z ⟶ X` and a 2-morphism `α : f ∘ x1 ⟶ f ∘ x2`, the
relative sheaf of isomorphisms from `x1` to `x2` is the 2-fibre product of
`Z ×_X Z ⟶ Z ×_Y Z` against the diagonal `Δ^α : Z ⟶ Z ×_Y Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The identity-on-`Z` cospan transformation with base `f`, sending the cospan
`x1, x2` to `x1 ≫ f, x2 ≫ f`. -/
def pairComparisonCospan {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} (x1 x2 : Z.toGroupoids ⟶ X) :
    CospanTransform x1 x2 (x1 ≫ f) (x2 ≫ f) :=
  CospanTransform.mk (𝟙 Z.toGroupoids) (𝟙 Z.toGroupoids) f
    (λ_ (x1 ≫ f)) (λ_ (x2 ≫ f))

/-- The comparison 1-morphism `Z ×_X Z ⟶ Z ×_Y Z` induced by `f`. -/
def pairComparison {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} (x1 x2 : Z.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  TwoFibreProduct.map (pairComparisonCospan f x1 x2)

/-- `pairComparison f x1 x2` is the two-fibre-product map of
`pairComparisonCospan f x1 x2`. -/
theorem pairComparison_eq {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} (x1 x2 : Z.toGroupoids ⟶ X) :
    pairComparison f x1 x2 = TwoFibreProduct.map (pairComparisonCospan f x1 x2) :=
  sorry

/-- The identity-leg cone presenting `Δ^α : Z ⟶ Z ×_{y1, Y, y2} Z`. -/
def diagonalAlphaCone {S : Scheme.{u}} {Y : GroupoidsOver S}
    {Z : AlgebraicSpace S} {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    Bicategory.PseudoPullbackCone y1 y2 where
  pt := Z.toGroupoids
  fst := 𝟙 Z.toGroupoids
  snd := 𝟙 Z.toGroupoids
  iso := λ_ y1 ≪≫ α ≪≫ (λ_ y2).symm

/-- The morphism `Δ^α : Z ⟶ Z ×_{y1, Y, y2} Z` determined by a 2-morphism
`α : y1 ⟶ y2`. -/
def diagonalAlpha {S : Scheme.{u}} {Y : GroupoidsOver S} {Z : AlgebraicSpace S}
    {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    Z.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} y1 y2 :=
  Bicategory.PseudoPullbackCone.lift (diagonalAlphaCone α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} y1 y2)

/-- First projection of `Δ^α` recovers the identity of `Z`. -/
def diagonalAlpha_fst {S : Scheme.{u}} {Y : GroupoidsOver S}
    {Z : AlgebraicSpace S} {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    diagonalAlpha α ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y1 y2 ≅
      𝟙 Z.toGroupoids :=
  Bicategory.PseudoPullbackCone.lift.fstIso (diagonalAlphaCone α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} y1 y2)

/-- Second projection of `Δ^α` recovers the identity of `Z`. -/
def diagonalAlpha_snd {S : Scheme.{u}} {Y : GroupoidsOver S}
    {Z : AlgebraicSpace S} {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    diagonalAlpha α ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} y1 y2 ≅
      𝟙 Z.toGroupoids :=
  Bicategory.PseudoPullbackCone.lift.sndIso (diagonalAlphaCone α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} y1 y2)

/-- The relative sheaf of isomorphisms `Isom^α_{X/Y}(x1, x2)`, as the 2-fibre
product of `Z ×_X Z ⟶ Z ×_Y Z` against `Δ^α`. -/
def relativeIsom {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α)

/-- `relativeIsom f α` is the 2-fibre product of `pairComparison f x1 x2`
against `diagonalAlpha α`. -/
theorem relativeIsom_eq {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (pairComparison f x1 x2) (diagonalAlpha α) :=
  sorry

/-- The relative isomorphism sheaf is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_relativeIsom
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    IsRepresentableByAlgebraicSpace (relativeIsom f α) :=
  sorry

/-- The sheaf of automorphisms of `x` when the target is the identity
fibration over `S`. -/
abbrev aut {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack (CategoryTheory.FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))]
    {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) : GroupoidsOver S :=
  relativeAut (baseProjection.{u + 1, u, u + 1} X) x

/-- `aut x` is relative automorphisms over the base projection of `X`. -/
theorem aut_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack (CategoryTheory.FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))]
    {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    aut x = relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  sorry

/-- The canonical 2-morphism between the structure maps of `x1` and `x2` over
the identity fibration. -/
def baseIso {S : Scheme.{u}} {X : GroupoidsOver S} {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) :
    x1 ≫ baseProjection.{u + 1, u, u + 1} X ≅
      x2 ≫ baseProjection.{u + 1, u, u + 1} X :=
  eqToIso (comp_baseProjection x1) ≪≫ (eqToIso (comp_baseProjection x2)).symm

/-- The sheaf of isomorphisms from `x1` to `x2` when the target is the identity
fibration over `S`. -/
abbrev isom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack (CategoryTheory.FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))]
    {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) : GroupoidsOver S :=
  relativeIsom (baseProjection.{u + 1, u, u + 1} X) (baseIso x1 x2)

/-- `isom x1 x2` is relative isomorphisms over the base projection of `X`,
using the canonical 2-cell between structure maps. -/
theorem isom_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack (CategoryTheory.FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))]
    {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) :
    isom x1 x2 =
      relativeIsom (baseProjection.{u + 1, u, u + 1} X) (baseIso x1 x2) :=
  sorry

/-- Absolute automorphisms of a morphism into an algebraic space `Y`. -/
abbrev autOn {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (x : Z.toGroupoids ⟶ X) : GroupoidsOver S :=
  relativeAut f x

/-- `autOn f x` is `relativeAut f x` when the target is an algebraic space. -/
theorem autOn_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (x : Z.toGroupoids ⟶ X) :
    autOn f x = relativeAut f x :=
  sorry

/-- Absolute isomorphisms of a pair of morphisms into an algebraic space `Y`. -/
abbrev isomOn {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    {f : X ⟶ Y.toGroupoids} (α : x1 ≫ f ≅ x2 ≫ f) : GroupoidsOver S :=
  relativeIsom f α

/-- `isomOn α` is `relativeIsom f α` when the target is an algebraic space. -/
theorem isomOn_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    {f : X ⟶ Y.toGroupoids} (α : x1 ≫ f ≅ x2 ≫ f) :
    isomOn α = relativeIsom f α :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
