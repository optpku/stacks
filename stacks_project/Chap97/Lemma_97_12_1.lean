module

public import stacks_project.Chap97.Lemma_97_12_1_Map
public import stacks_project.Chap95.«95_18_2_1_Forgetful»

/-!
# Lemma 97.12.1

A 2-commutative square of stacks in groupoids over `(Sch/S)_fppf` induces a
canonical 1-morphism of finite Hilbert stacks, compatible with the forgetful
1-morphisms of Equation 95.18.2.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.12.1 (1): a 2-commutative square of stacks in groupoids over
`(Sch/S)_fppf` with 2-isomorphism `γ : F' ≫ H ≅ G ≫ F` induces a canonical
1-morphism `H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)`. -/
@[stacks 05XN]
def finiteHilbertMapSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    stack (toGroupoidsMor F') d ⟶ stack (toGroupoidsMor F) d :=
  mapSquare F' F G H γ d

/-- Lemma 97.12.1 (2): the induced 1-morphism is compatible with the forgetful
1-morphisms `H_d(𝒳/𝒴) ⟶ H_d` of Equation 95.18.2.1. -/
@[stacks 05XN]
theorem finiteHilbertMapSquare_comp_forgetToPoint (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToPoint F d =
      forgetToPoint F' d :=
  sorry

/-- Lemma 97.12.1 (3): the induced 1-morphism is compatible with the forgetful
1-morphisms `H_d(𝒳/𝒴) ⟶ H_d(𝒳)` of Equation 95.18.2.1. -/
@[stacks 05XN]
theorem finiteHilbertMapSquare_comp_forgetToAbsolute (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToAbsolute F d =
      forgetToAbsolute F' d ≫ mapSquareAbsolute G d :=
  sorry

/-- Lemma 97.12.1 (4): the induced 1-morphism is compatible with the forgetful
1-morphisms `H_d(𝒳/𝒴) ⟶ 𝒴` of Equation 95.18.2.1. -/
@[stacks 05XN]
theorem finiteHilbertMapSquare_comp_forgetToY (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d =
      forgetToY F' d ≫ H :=
  sorry

end AlgebraicGeometry
