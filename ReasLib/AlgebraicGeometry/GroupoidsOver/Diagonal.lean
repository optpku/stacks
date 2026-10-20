module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Representable diagonal of a category fibred in groupoids

For a category fibred in groupoids over `(Sch/S)_fppf`, representability of the
diagonal by algebraic spaces is equivalent to algebraic-space Isom sheaves,
relative representability of Yoneda slices, and the corresponding statements
for 2-fibre products and for scheme-representable or space-representable test
objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The isomorphism presheaf `Isom(x, y)` on `(Over U)^op`, reindexed along
`U.iteratedSliceEquiv` to a presheaf on schemes over `U.left`. -/
def isomorphismPresheaf.overLeft {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (x y : X.p.Fiber U) : (Over U.left)ᵒᵖ ⥤ Type u :=
  U.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y

/-- `overLeft x y` is precomposition of `Functor.isomorphismPresheaf X.p x y`
with the opposite of the iterated-slice inverse. -/
theorem isomorphismPresheaf.overLeft_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (x y : X.p.Fiber U) :
    isomorphismPresheaf.overLeft x y =
      U.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y :=
  rfl

/-- The transported isomorphism presheaf at a pair of fibre objects is an
algebraic space over `U`. -/
def isomorphismPresheaf.isAlgebraicSpaceAt {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (x y : X.p.Fiber U) : Prop :=
  AlgebraicSpace.IsAlgebraicSpace (isomorphismPresheaf.overLeft x y)

/-- Being an algebraic space over `U` means some algebraic space over `U.left`
has functor of points isomorphic to `overLeft x y`. -/
theorem isomorphismPresheaf.isAlgebraicSpaceAt_iff {S : Scheme.{u}}
    {X : GroupoidsOver S} {U : Over S} (x y : X.p.Fiber U) :
    isomorphismPresheaf.isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace U.left,
        Nonempty (isomorphismPresheaf.overLeft x y ≅ F.functorOfPoints) :=
  sorry

/-- Every pair of fibre objects has an algebraic-space isomorphism presheaf over
its base. -/
def isomorphismPresheaf.isAlgebraicSpace {S : Scheme.{u}}
    (X : GroupoidsOver S) : Prop :=
  ∀ ⦃U : Over S⦄ (x y : X.p.Fiber U), isomorphismPresheaf.isAlgebraicSpaceAt x y

/-- The global algebraic-space Isom condition unfolds to
`isAlgebraicSpaceAt` at every fibre pair. -/
theorem isomorphismPresheaf.isAlgebraicSpace_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) :
    isomorphismPresheaf.isAlgebraicSpace X ↔
      ∀ ⦃U : Over S⦄ (x y : X.p.Fiber U),
        isomorphismPresheaf.isAlgebraicSpaceAt x y := by
  rfl

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if for every scheme `U` over `S` and objects `x, y` of the
fibre `X_U`, the sheaf `Isom(x, y)` is an algebraic space over `U`. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_isom
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      isomorphismPresheaf.isAlgebraicSpace X :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if for every scheme `U` over `S` and object `x` of the fibre
`X_U`, the associated 1-morphism `YonedaSlice.representative x` is representable
by algebraic spaces. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃U : Over S⦄ (x : X.p.Fiber U),
        relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x) :=
  sorry

/-- If the diagonal of `X` is representable by algebraic spaces, then every
Yoneda slice 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.yoneda_of_diagonal
    {S : Scheme.{u}} {X : GroupoidsOver S}
    (h : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {U : Over S} (x : X.p.Fiber U) :
    relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x) :=
  sorry

/-- If every Yoneda slice 1-morphism of `X` is representable by algebraic spaces,
then the diagonal of `X` is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_of_yoneda
    {S : Scheme.{u}} {X : GroupoidsOver S}
    (h : ∀ ⦃U : Over S⦄ (x : X.p.Fiber U),
      relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x)) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

/-- Relative representability of the diagonal is equivalent to relative
representability of every 1-morphism out of a scheme slice. -/
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_slice
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃U : Over S⦄ (G : GroupoidsOver.slice U ⟶ X),
        relativelyRepresentableByAlgebraicSpaces G :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if for every pair of schemes `T₁, T₂` over `S` and objects
`xᵢ` of `X_{Tᵢ}`, the 2-fibre product of the associated Yoneda 1-morphisms is
representable by an algebraic space. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_slicePair
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃T₁ T₂ : Over S⦄ (x₁ : X.p.Fiber T₁) (x₂ : X.p.Fiber T₂),
        IsRepresentableByAlgebraicSpace
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (YonedaSlice.representative x₁) (YonedaSlice.representative x₂)) :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if every 1-morphism to `X` from a representable category
fibred in groupoids over `(Sch/S)_fppf` is representable by algebraic spaces. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofRepresentable
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {U : GroupoidsOver S} (f : U ⟶ X),
        FiberedCategoryOver.Groupoids.IsRepresentable U →
          relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if for every pair of representable categories fibred in
groupoids `T₁, T₂` and 1-morphisms `xᵢ : Tᵢ ⟶ X`, the 2-fibre product
`T₁ ×_{x₁, X, x₂} T₂` is representable by an algebraic space. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofRepresentablePair
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {T₁ T₂ : GroupoidsOver S} (x₁ : T₁ ⟶ X) (x₂ : T₂ ⟶ X),
        FiberedCategoryOver.Groupoids.IsRepresentable T₁ →
          FiberedCategoryOver.Groupoids.IsRepresentable T₂ →
            IsRepresentableByAlgebraicSpace
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} x₁ x₂) :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if every 1-morphism to `X` from a category fibred in
groupoids representable by an algebraic space is representable by algebraic
spaces. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofAlgebraicSpace
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {U : GroupoidsOver S} (f : U ⟶ X),
        IsRepresentableByAlgebraicSpace U →
          relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- The diagonal `X ⟶ X × X` is representable by algebraic
spaces if and only if for every pair of categories fibred in groupoids `T₁, T₂`
representable by algebraic spaces and 1-morphisms `xᵢ : Tᵢ ⟶ X`, the 2-fibre
product `T₁ ×_{x₁, X, x₂} T₂` is representable by an algebraic space. -/
@[stacks 045G]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofAlgebraicSpacePair
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {T₁ T₂ : GroupoidsOver S} (x₁ : T₁ ⟶ X) (x₂ : T₂ ⟶ X),
        IsRepresentableByAlgebraicSpace T₁ →
          IsRepresentableByAlgebraicSpace T₂ →
            IsRepresentableByAlgebraicSpace
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} x₁ x₂) :=
  sorry

end AlgebraicGeometry
