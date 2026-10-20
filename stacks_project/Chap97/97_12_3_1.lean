module

public import stacks_project.Chap97.Lemma_97_12_1_Map
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

section
variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴 :
  StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
variable (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
variable (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ) (hd : 1 ≤ d)
variable [AlgebraicGeometry.Groupoids.Hom.Etale
  (CategoryTheory.StackOver.Groupoids.Hom.toGroupoidsMor G)]
variable {U : Over S}
variable (ξ : (AlgebraicGeometry.FiniteHilbertStack.stack
  (CategoryTheory.StackOver.Groupoids.Hom.toGroupoidsMor F) d).p.Fiber U)

/- 97.12.3.1: the displayed 2-fibre product
`(Sch/U)_fppf ×_{ξ, ℋ_d(𝒳/𝒴)} ℋ_d(𝒳'/𝒴)` is
the apex in `GroupoidsOver S` of the concrete finite Hilbert-stack cospan.
The first leg is the Yoneda representative of the fibre object `ξ` over `U`.
The second leg is the canonical morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)`
induced by the identity-base square with comparison cell `γ`, for positive
degree `d` and representable étale `G`. -/
@[stacks 05XT]
#check (CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u}
  (CategoryTheory.FiberedCategoryOver.Groupoids.YonedaSlice.representative ξ)
  (CategoryTheory.StackOver.Groupoids.Hom.toGroupoidsMor
    (AlgebraicGeometry.FiniteHilbertStack.mapSquare F' F G (𝟙 𝒴) γ d)) :
  AlgebraicGeometry.GroupoidsOver S)
end
