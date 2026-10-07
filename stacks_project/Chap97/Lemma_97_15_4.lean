module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap97.Lemma_97_7_1_SurjectiveOnObjects
public import stacks_project.Chap97.Lemma_97_15_4_Lci
public import stacks_project.Chap97.Lemma_97_15_4_Coproduct
public import stacks_project.Chap100.Lemma_100_3_3

/-!
# Lemma 97.15.4

If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
that is representable by algebraic spaces, flat, surjective, and locally of
finite presentation, then the coproduct 1-morphism
`∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is surjective on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.15.4: if `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` that is representable by algebraic spaces, flat, surjective, and
locally of finite presentation, then the coproduct forgetful 1-morphism
`lciCoproduct.forgetToY F : ∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is surjective on
objects. The hypotheses `Flat`, `Surjective`, and `LocallyOfFinitePresentation`
each include relative representability by algebraic spaces. -/
@[stacks 06DA]
instance lciCoproduct.forgetToY.surjectiveOnObjects (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    Groupoids.Hom.SurjectiveOnObjects
      (asGroupoidsOverMor (lciCoproduct.forgetToY F)) :=
  sorry

/-- Every field-valued object of `𝒴` over `Spec(k)` lifts to an LCI Hilbert
object of some degree `d ≥ 1` with the same test scheme `Spec(k)`, so no field
extension is required. -/
theorem exists_lciObj_over_field (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)]
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ asGroupoidsOver 𝒴) :
    ∃ (d : ℕ) (_ : 0 < d) (ξ : Obj (asGroupoidsOverMor F) d)
      (hU : ξ.U = Over.mk σ),
      Obj.IsLci (asGroupoidsOverMor F) ξ ∧
        Nonempty
          (YonedaSlice.representative ξ.y ≅
            slice.pullback (eqToHom hU) y) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
