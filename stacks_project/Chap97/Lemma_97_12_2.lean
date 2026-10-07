module

public import stacks_project.Chap97.Lemma_97_12_1
public import stacks_project.Chap97.Lemma_97_12_2_Cone

/-!
# Lemma 97.12.2

A 2-cartesian square of stacks in groupoids over `(Sch/S)_fppf` remains
2-cartesian after applying finite Hilbert stacks in degree `d` and the
forgetful 1-morphisms to the base stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.12.2: in the situation of Lemma 97.12.1, if the given square is
2-cartesian, then the diagram with apex `H_d(𝒳'/𝒴')`, horizontal map
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)`, vertical forgetful maps to `𝒴'` and `𝒴`, and
bottom map `H` is 2-cartesian. -/
@[stacks 05XP, instance]
theorem forgetToYSquare_isBilimit (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    [(⟨𝒳', F', G, γ⟩ : PseudoPullbackCone H F).IsBilimit] :
    (forgetToYSquare F' F G H γ d
        (eqToIso (finiteHilbertMapSquare_comp_forgetToY F' F G H γ d).symm)).IsBilimit :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
