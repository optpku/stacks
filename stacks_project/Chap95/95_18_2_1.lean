module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
import StacksCheckRecall

/-!
# Equation 95.18.2.1

The source considers degree `d ≥ 1`. The four canonical forgetful morphisms
also exist at every natural rank: their formulas preserve the finite locally
free scheme and do not require a positive-rank covering.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

/- 95.18.2.1 (1): The absolute-to-base Hilbert morphism. -/
@[stacks 05WD] #check (AlgebraicGeometry.FiniteHilbertStack.absoluteToPoint :
  ∀ {S : Scheme.{u}} (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ),
    ofStack 𝒳.toGroupoids d ⟶ ofScheme S d)

/- 95.18.2.1 (2): The relative-to-base Hilbert morphism. -/
@[stacks 05WD] #check (AlgebraicGeometry.FiniteHilbertStack.forgetToPoint :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ ofScheme S d)

/- 95.18.2.1 (3): The relative-to-absolute Hilbert morphism. -/
@[stacks 05WD] #check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ ofStack 𝒳.toGroupoids d)

/- 95.18.2.1 (4): The projection to the target stack. -/
@[stacks 05WD] #check (AlgebraicGeometry.FiniteHilbertStack.forgetToY :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ 𝒴)

#check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute_comp_absoluteToPoint :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute F d ≫
      AlgebraicGeometry.FiniteHilbertStack.absoluteToPoint 𝒳 d =
        AlgebraicGeometry.FiniteHilbertStack.forgetToPoint F d)
