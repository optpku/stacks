module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/- Exercise 111.38.2: for a field `k`, every morphism
`φ : Spec (RatFunc k) ⟶ scheme k n` over `k` extends along
`Spec.map` of the inclusion `Polynomial k → RatFunc k` to a morphism
`ψ : Spec (Polynomial k) ⟶ scheme k n` over `k`. -/
@[stacks 0DJ2] #check (AlgebraicGeometry.ProjectiveSpace.exists_hom_fromPolynomial :
  ∀ {k : Type u} [Field k] {n : ℕ}
    (φ : Spec (CommRingCat.of (RatFunc k)) ⟶ scheme k n)
    (h_over : φ ≫ toSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))),
    ∃ ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ scheme k n,
      ψ ≫ toSpec k n =
          Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (RatFunc k))) ≫
            ψ = φ)

end AlgebraicGeometry.ProjectiveSpace
