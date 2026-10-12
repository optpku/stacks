/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Pseudofunctor.Construction

/-!
# Action of the fibred-category two-fibre-product pseudofunctor

These lemmas expose the object, `1`-cell, `2`-cell, comparison, and hom-functor actions through
the application-facing two-fibre-product API.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

/-- The object action of the bundled-cospan pseudofunctor is the application-facing explicit
two-fibre-product apex. -/
@[simp]
theorem pseudofunctor.obj
    (S : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor (C := C)).obj S = apex S.fst S.snd := sorry

/-- The `1`-cell action of the bundled-cospan pseudofunctor is the application-facing
componentwise map. -/
@[simp]
theorem pseudofunctor.map
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor (C := C)).map ψ =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The `2`-cell action of the bundled-cospan pseudofunctor is heterogeneously equal to the
application-facing action on cospan modifications. -/
theorem pseudofunctor.map₂
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor (C := C)).map₂ Γ ≍
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map₂
        (Bicategory.Cospan.Hom₂.toModification Γ) := sorry

/-- The identity comparison of the bundled-cospan pseudofunctor is the canonical
application-facing identity comparison. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor (C := C)).mapId S =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.idIso
        S.fst S.snd := sorry

/-- The composition comparison of the bundled-cospan pseudofunctor is the canonical
application-facing composition comparison. -/
@[simp]
theorem pseudofunctor.mapComp
    {R S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor (C := C)).mapComp ψ φ =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.compIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)
        (Bicategory.Cospan.Hom.toCospanTransform φ) := sorry

/-- On each hom category, the bundled-cospan pseudofunctor is the cospan-inclusion hom functor
followed by the application-facing hom functor on two-fibre-product maps. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor (C := C)).mapFunctor S T =
      (Bicategory.Cospan.inclusion
          (B := FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)).mapFunctor
          S T ⋙
        _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.mapFunctor
          (F₁ := S.fst) (G₁ := S.snd) (F₂ := T.fst) (G₂ := T.snd) := sorry

/-- The object action of the bundled-cospan hom functor is the application-facing map of the
underlying cospan transformation. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    ((pseudofunctor (C := C)).mapFunctor S T).obj ψ =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The morphism action of the bundled-cospan hom functor is heterogeneously equal to the
application-facing action on cospan modifications. -/
theorem pseudofunctor.mapFunctor.map
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    ((pseudofunctor (C := C)).mapFunctor S T).map Γ ≍
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map₂
        (Bicategory.Cospan.Hom₂.toModification Γ) := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
