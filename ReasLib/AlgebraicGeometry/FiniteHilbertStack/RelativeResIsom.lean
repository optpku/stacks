/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Product
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

namespace AlgebraicGeometry

namespace FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The two-fibre product of the slice represented by `U` with the relative
finite Hilbert stack over the product of the absolute finite Hilbert stack and
`𝒴`, along the Yoneda representatives of `ξ` and `y` and the two forgetful
morphisms. -/
noncomputable def relativeResIsom (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

/-- `relativeResIsom` is the 2-fibre product of `ξ × y` with the forgetful map
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`. -/
theorem relativeResIsom_eq (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
        (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
          (asGroupoidsOverMor (forgetToY F d))) :=
  rfl

/-- `relativeResIsom F d ξ y` is the apex of the canonical 2-fibre-product cone of
`ξ × y` and the forgetful map `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`. -/
theorem relativeResIsom_spec (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
        (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
          (asGroupoidsOverMor (forgetToY F d)))).pt =
      relativeResIsom F d ξ y :=
  rfl

/-- First projection of `relativeResIsom F d ξ y`, to `(Sch/U)_fppf`. -/
noncomputable abbrev relativeResIsom.fst (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y ⟶ GroupoidsOver.slice U :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

/-- Second projection of `relativeResIsom F d ξ y`, to `ℋ_d(𝒳/𝒴)`. -/
noncomputable abbrev relativeResIsom.snd (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y ⟶ asGroupoidsOver (stack (asGroupoidsOverMor F) d) :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

end FiniteHilbertStack

end AlgebraicGeometry
