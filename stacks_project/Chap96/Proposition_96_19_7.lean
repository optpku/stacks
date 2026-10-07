module

public import stacks_project.Chap96.Lemma_96_19_6_Covering
public import stacks_project.Chap96.Proposition_96_19_7_ExtendedSheaf

/-!
# Exactness of the extended relative Čech complex of an abelian sheaf
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Proposition 96.19.7: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.
If `F` is an abelian sheaf on `𝒳_τ`, and every object of `𝒳` admits a covering
`{xᵢ ⟶ x}` in `𝒳_τ` such that each `xᵢ` is isomorphic to `f(uᵢ)` for some
object `uᵢ` of `𝒰`, then the extended relative Čech complex
`RelativeCech.extendedSheaf f τ F` is exact in `Ab(𝒳_τ)`. -/
@[stacks 06XE]
theorem relativeCechExtended_acyclic (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    (hf : coversByEssentialImage f τ) :
    (RelativeCech.extendedSheaf f τ F).Acyclic :=
  sorry

end AlgebraicGeometry.GroupoidsOver
