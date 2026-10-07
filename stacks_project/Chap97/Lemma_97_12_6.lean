module

public import stacks_project.Chap97.«97_12_6_1_Map»
public import stacks_project.Chap97.«97_12_6_1_Pullback»
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Lemma 97.12.6

If `F : 𝒳 ⟶ 𝒴` and `G : 𝒳' ⟶ 𝒳` are 1-morphisms of stacks in groupoids over
`(Sch/S)_fppf` and `G` is representable by algebraic spaces, then the induced
1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X' X Y : GroupoidsOver S}
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
variable [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]

/-- Lemma 97.12.6: Let `F : 𝒳 ⟶ 𝒴` and `G : 𝒳' ⟶ 𝒳` be 1-morphisms of stacks
in groupoids over `(Sch/S)_fppf`. If `G` is representable by algebraic spaces,
then the 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic
spaces. -/
@[stacks 05YJ]
theorem map.relativelyRepresentableByAlgebraicSpaces
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ)
    (hG : relativelyRepresentableByAlgebraicSpaces G) :
    relativelyRepresentableByAlgebraicSpaces (map G F d) := sorry

/-- The displayed 2-fibre product `(Sch/U)_fppf ×_ξ H_d(𝒳'/𝒴)` along a Yoneda
test `ξ` of `H_d(𝒳/𝒴)` admits a representing algebraic space over `U`. -/
theorem twoFibreProduct.represents (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ)
    (hG : relativelyRepresentableByAlgebraicSpaces G) {U : Over S}
    (ξ : (toGroupoids F d).p.Fiber U) :
    ∃ (W : AlgebraicSpace S) (fW : W ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange (map G F d) (YonedaSlice.representative ξ) W fW :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
