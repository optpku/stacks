module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Fibre-product comparison along a morphism of algebraic stacks

A 1-morphism `f : X ⟶ Y` induces `T1 ×_X T2 ⟶ T1 ×_Y T2` as the
`TwoFibreProduct.map` of the identity-on-`Tᵢ` cospan transformation with base
`f`. Scheme-slice tests of this comparison are tests of the relative
2-diagonal of `f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The identity-on-`Tᵢ` cospan transformation with base `f`, sending the cospan
`x1, x2` to `x1 ≫ f, x2 ≫ f`. -/
def fibreProductCospan {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    CospanTransform x1 x2 (x1 ≫ f) (x2 ≫ f) :=
  CospanTransform.mk (𝟙 T1.toGroupoids) (𝟙 T2.toGroupoids) f
    (λ_ (x1 ≫ f)) (λ_ (x2 ≫ f))

/-- The left vertex of `fibreProductCospan f x1 x2` is the identity of `T1`. -/
theorem fibreProductCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).left = 𝟙 T1.toGroupoids :=
  sorry

/-- The right vertex of `fibreProductCospan f x1 x2` is the identity of `T2`. -/
theorem fibreProductCospan_right {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).right = 𝟙 T2.toGroupoids :=
  sorry

/-- The base vertex of `fibreProductCospan f x1 x2` is `f`. -/
theorem fibreProductCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).base = f :=
  sorry

/-- The left generating comparison of `fibreProductCospan f x1 x2` is the left
unitor of `x1 ≫ f`. -/
theorem fibreProductCospan_leftIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).leftIso = λ_ (x1 ≫ f) :=
  sorry

/-- The right generating comparison of `fibreProductCospan f x1 x2` is the left
unitor of `x2 ≫ f`. -/
theorem fibreProductCospan_rightIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).rightIso = λ_ (x2 ≫ f) :=
  sorry

/-- The comparison 1-morphism `T1 ×_X T2 ⟶ T1 ×_Y T2` induced by `f`. -/
def fibreProductComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  TwoFibreProduct.map (fibreProductCospan f x1 x2)

/-- `fibreProductComparison f x1 x2` is the two-fibre-product map of
`fibreProductCospan f x1 x2`. -/
theorem fibreProductComparison_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    fibreProductComparison f x1 x2 =
      TwoFibreProduct.map (fibreProductCospan f x1 x2) :=
  sorry

/-- The cospan transformation `(x1 ≫ f, x2 ≫ f) ⟶ (f, f)` with vertices `x1`,
`x2` and identity on `Y`. -/
def pairToDiagonalCospan {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    CospanTransform (x1 ≫ f) (x2 ≫ f) f f :=
  CospanTransform.mk x1 x2 (𝟙 Y) (ρ_ (x1 ≫ f)).symm (ρ_ (x2 ≫ f)).symm

/-- The left vertex of `pairToDiagonalCospan f x1 x2` is `x1`. -/
theorem pairToDiagonalCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (pairToDiagonalCospan f x1 x2).left = x1 :=
  sorry

/-- The right vertex of `pairToDiagonalCospan f x1 x2` is `x2`. -/
theorem pairToDiagonalCospan_right {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (pairToDiagonalCospan f x1 x2).right = x2 :=
  sorry

/-- The base vertex of `pairToDiagonalCospan f x1 x2` is the identity of `Y`. -/
theorem pairToDiagonalCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    (pairToDiagonalCospan f x1 x2).base = 𝟙 Y :=
  sorry

/-- The right vertical of the source cartesian square, sending
`T1 ×_Y T2` to `X ×_Y X`. -/
def pairToDiagonal {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f :=
  TwoFibreProduct.map (pairToDiagonalCospan f x1 x2)

/-- `pairToDiagonal f x1 x2` is the two-fibre-product map of
`pairToDiagonalCospan f x1 x2`. -/
theorem pairToDiagonal_eq {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    pairToDiagonal f x1 x2 = TwoFibreProduct.map (pairToDiagonalCospan f x1 x2) :=
  sorry

/-- A scheme-slice test of `fibreProductComparison f x1 x2` is a scheme-slice
test of the relative 2-diagonal of `f`. -/
theorem fibreProductComparison_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) (P : MorphismProperty (AlgebraicSpace S))
    (hP : Groupoids.Hom.has P (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has P (fibreProductComparison f x1 x2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
