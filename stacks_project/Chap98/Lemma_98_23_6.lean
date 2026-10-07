module

public import stacks_project.Chap98.Lemma_98_23_6_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.23.6

Functoriality of a naive obstruction theory induces bijections on
`H^i(- ⊗^L k)` in degrees `0` and `1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- Lemma 98.23.6. Let `S` and `X` be as in Definition 98.23.5 and let `X` be
endowed with a naive obstruction theory. Let `A → B` and `y → x` be as in (3).
Let `k` be a `B`-algebra which is a field. Then the functoriality map
`E_x ⟶ E_y` induces bijections
`H^i(E_x ⊗_A^L k) ⟶ H^i(E_y ⊗_B^L k)` for `i = 0, 1`. -/
@[stacks 07YT]
theorem homologyMapAlong_bijective (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [Field k] [Algebra η.carrier k]
    (i : ℤ) (hi : i = 0 ∨ i = 1) :
    Function.Bijective (ModuleCat.Hom.hom (homologyMapAlong 𝒪 f k i)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory
