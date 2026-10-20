module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Algebraic morphisms of groupoid fibrations

A 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic when every
slice 2-fibre product against an object of the target is an algebraic stack
over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism `F : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` is algebraic when, for every scheme `T` over `S` and every
1-morphism `ξ : GroupoidsOver.slice T ⟶ Y`, the 2-fibre product
`TwoFibreProduct.apex ξ F` is an algebraic stack over `S`. -/
class Algebraic {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) : Prop where
  /-- Every slice 2-fibre product of `F` is an algebraic stack over `S`. -/
  algebraicStack_twoFibreProduct :
    ∀ ⦃T : Over S⦄ (ξ : GroupoidsOver.slice T ⟶ Y),
      AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ F)

namespace Algebraic

/-- The identity 1-morphism of a category fibred in groupoids is algebraic. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Algebraic (𝟙 X) := sorry

/-- The slice 2-fibre product of an algebraic 1-morphism is an algebraic stack
over `S`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) [Algebraic F]
    {T : Over S} (ξ : GroupoidsOver.slice T ⟶ Y) :
    AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ F) := sorry

/-- A 1-morphism is algebraic if and only if every slice 2-fibre product is an
algebraic stack over `S`. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) :
    Algebraic F ↔
      ∀ ⦃T : Over S⦄ (ξ : GroupoidsOver.slice T ⟶ Y),
        AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ F) := sorry

/-- A 1-morphism is algebraic if and only if every 2-fibre product against the
Yoneda representative of an object of `Y` over a scheme `T` is an algebraic
stack over `S`. -/
theorem iff_yonedaRepresentative {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (F : X ⟶ Y) :
    Algebraic F ↔
      ∀ (T : Over S) (ξ : Y.p.Fiber T),
        AlgebraicStack
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ) F) := sorry

/-- A 1-morphism of stacks in groupoids over `(Sch/S)_fppf` from an algebraic
stack to a stack whose diagonal is representable by algebraic spaces is algebraic. -/
theorem of_algebraicStack
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y)
    (hY : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)) :
    Algebraic F :=
  sorry

end Algebraic

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry

/-- If an algebraic 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
has target diagonal representable by algebraic spaces, then its source diagonal
is representable by algebraic spaces. -/
@[stacks 0D3R]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_of_algebraic
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Groupoids.Hom.Algebraic F]
    (hY : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry
