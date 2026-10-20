module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Product

/-!
# The forgetful pairing of finite Hilbert stacks

The relative finite Hilbert stack maps canonically to the product of the
absolute finite Hilbert stack and the target stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The forgetful pairing `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`, as the universal lift of
the two forgetful morphisms into the two-fibre product of the base projections. -/
noncomputable def forgetToProduct (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    asGroupoidsOver (stack (asGroupoidsOverMor F) d) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
        (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) :=
  pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d)) (asGroupoidsOverMor (forgetToY F d))

/-- The forgetful pairing is `pairOverBase` of the two forgetful morphisms. -/
theorem forgetToProduct_eq (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d =
      pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
        (asGroupoidsOverMor (forgetToY F d)) :=
  rfl

/-- The first projection of `forgetToProduct F d` is isomorphic to
`asGroupoidsOverMor (forgetToAbsolute F d)`. -/
noncomputable def forgetToProduct_fst (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) ≅
      asGroupoidsOverMor (forgetToAbsolute F d) :=
  pairOverBase_fst (asGroupoidsOverMor (forgetToAbsolute F d))
    (asGroupoidsOverMor (forgetToY F d))

/-- The second projection of `forgetToProduct F d` is isomorphic to
`asGroupoidsOverMor (forgetToY F d)`. -/
noncomputable def forgetToProduct_snd (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) ≅
      asGroupoidsOverMor (forgetToY F d) :=
  pairOverBase_snd (asGroupoidsOverMor (forgetToAbsolute F d))
    (asGroupoidsOverMor (forgetToY F d))

end AlgebraicGeometry.FiniteHilbertStack
