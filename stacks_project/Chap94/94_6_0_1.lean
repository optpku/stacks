module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.FullyFaithful

/-!
# Representable 1-morphisms: the 2-Yoneda diagram
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory TwoFibreProduct

universe u

namespace AlgebraicGeometry

/-- 94.6.0.1: let `S` be a scheme and let `X`, `Y` be categories fibred in groupoids
over `(Sch/S)_fppf`. Given a 1-morphism `f : X ⟶ Y`, objects `U`, `V` of `Over S`,
a test 1-morphism `y : slice U ⟶ Y`, and a chosen equivalence
`e : slice V ≌ y ⊡₂ f`, the recovered morphism
`slice.eval (e.hom ≫ TwoFibreProduct.fst y f) : V ⟶ U` is the scheme map `f_y`
in the displayed 2-commutative diagram. Squiggly arrows are the 2-Yoneda embeddings
`slice`; the middle vertical is `overMap f_y`; the right square is the 2-fibre-product
cone of `f` along `y`, with comparison `TwoFibreProduct.comparisonIso y f`. -/
@[stacks 0401]
theorem relativelyRepresentable.overMap_eval_fst
    {S : Scheme.{u}} {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {f : X ⟶ Y} {U V : Over S} (y : slice U ⟶ Y)
    (e : slice V ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f) :
    Nonempty
      (overMap (slice.eval (e.hom ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)) ≅
        e.hom ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f) := sorry

/-- A relatively representable 1-morphism admits a slice presentation of each
2-fibre product along a test 1-morphism from a slice. -/
theorem relativelyRepresentable.exists_slicePresentation
    {S : Scheme.{u}} {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {f : X ⟶ Y} (hf : relativelyRepresentable f) {U : Over S} (y : slice U ⟶ Y) :
    ∃ V : Over S, Nonempty (slice V ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f) := sorry

end AlgebraicGeometry
