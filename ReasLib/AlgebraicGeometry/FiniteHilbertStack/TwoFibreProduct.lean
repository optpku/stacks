/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Stack
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Map

/-!
# Slice 2-fibre product of a finite Hilbert stack along a Yoneda representative

The object `(Sch/U)_fppf ×_{ξ, H_d(X/Y)} H_d(X'/Y)` is the canonical
2-fibre product of the Yoneda 1-morphism of `ξ` with the Hilbert 1-morphism
induced by `G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X' X Y : GroupoidsOver S}

/-- The 2-fibre product `(Sch/U)_fppf ×_{ξ, H_d(X/Y)} H_d(X'/Y)` of the Yoneda
1-morphism of an object `ξ` of `H_d(X/Y)` over `U` with the 1-morphism
`H_d(X'/Y) ⟶ H_d(X/Y)` induced by `G`. -/
abbrev twoFibreProduct
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ) (map G F d)

/-- `twoFibreProduct` is the 2-fibre product of the Yoneda representative of `ξ`
with `map G F d`. -/
theorem twoFibreProduct_eq
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) :
    twoFibreProduct G F d ξ =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ) (map G F d) := sorry

/-- First projection of the Yoneda base change, to `(Sch/U)_fppf`. -/
abbrev twoFibreProduct.fst
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) :
    twoFibreProduct G F d ξ ⟶ GroupoidsOver.slice U :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ) (map G F d)

/-- Second projection of the Yoneda base change, to `H_d(X'/Y)`. -/
abbrev twoFibreProduct.snd
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) :
    twoFibreProduct G F d ξ ⟶ toGroupoids (G ≫ F) d :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ) (map G F d)

end AlgebraicGeometry.FiniteHilbertStack
