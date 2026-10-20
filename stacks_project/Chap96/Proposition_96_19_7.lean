module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.Exactness
import StacksCheckRecall

/-!
# Exactness of the extended relative Čech complex of an abelian sheaf
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Proposition 96.19.7: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.
If `F` is an abelian sheaf on `𝒳_τ`, and every object of `𝒳` admits a covering
`{xᵢ ⟶ x}` in `𝒳_τ` such that each `xᵢ` is isomorphic to `f(uᵢ)` for some
object `uᵢ` of `𝒰`, then the extended relative Čech complex
`RelativeCech.extendedSheaf f τ F` is exact in `Ab(𝒳_τ)`, including its initial
term `F`. -/
@[stacks 06XE]
#check (AlgebraicGeometry.GroupoidsOver.relativeCechExtended_acyclic :
  ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}],
    AlgebraicGeometry.GroupoidsOver.coversByEssentialImage f τ →
      (RelativeCech.extendedSheaf f τ F).Acyclic)
