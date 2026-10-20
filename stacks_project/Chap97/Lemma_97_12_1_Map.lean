module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Square

/-!
# Compatibility name for square-induced finite Hilbert morphisms

The historical component name forwards to the canonical construction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Compatibility abbreviation for the canonical morphism induced by a 2-commutative square. -/
abbrev mapSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    stack (toGroupoidsMor F') d ⟶ stack (toGroupoidsMor F) d :=
  AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d

end AlgebraicGeometry.FiniteHilbertStack

#check (AlgebraicGeometry.finiteHilbertMapSquare :
  {S : Scheme.{u}} →
  {𝒳' 𝒳 𝒴' 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u}
    (Scheme.fppfTopology.over S)} →
  (F' : 𝒳' ⟶ 𝒴') → (F : 𝒳 ⟶ 𝒴) → (G : 𝒳' ⟶ 𝒳) → (H : 𝒴' ⟶ 𝒴) →
  (γ : F' ≫ H ≅ G ≫ F) → (d : ℕ) →
  FiniteHilbertStack.stack (toGroupoidsMor F') d ⟶
    FiniteHilbertStack.stack (toGroupoidsMor F) d)
