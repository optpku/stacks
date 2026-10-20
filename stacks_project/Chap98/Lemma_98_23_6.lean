module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory.BaseChange
import StacksCheckRecall

/-!
# Lemma 98.23.6

Functoriality of a naive obstruction theory induces bijections on
`H^i(- ⊗^L k)` in degrees `0` and `1`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 98.23.6. Let `S` and `X` be as in Definition 98.23.5 and let `X` be
endowed with a naive obstruction theory. Let `A → B` and `y → x` be as in (3).
Let `k` be a `B`-algebra which is a field. Then the functoriality map
`E_x ⟶ E_y` induces bijections
`H^i(E_x ⊗_A^L k) ⟶ H^i(E_y ⊗_B^L k)` for `i = 0, 1`. -/
@[stacks 07YT] #check
  (AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory.homologyMapAlong_bijective :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
      (𝒪 : NaiveObstructionTheory X)
      {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
      (k : Type u) [Field k] [Algebra η.carrier k]
      (i : ℤ), i = 0 ∨ i = 1 →
      Function.Bijective
        (ModuleCat.Hom.hom (NaiveObstructionTheory.homologyMapAlong 𝒪 f k i)))
