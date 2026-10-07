module

public import stacks_project.Chap82.Lemma_82_10_4_Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
variable (hf : f ≫ pY = pX) (k : ℤ)
variable (Z : ClosedSubspace Y) [IsIntegral Z.X]
  (hZ : pY.closedSubspaceDeltaDimension δ Z = (k : EInt))
variable (α : Function.locallyFinsupp (Points Y) ℤ)

/- Definition 82.10.1 (1): In Situation 82.2.1, for good `X, Y / B` and a
morphism `f : X ⟶ Y` over `B` that is flat of relative dimension `r`, if
`Z ⊂ Y` is an integral closed subspace of `δ`-dimension `k`, then `f^*[Z]`
is the associated `(k + r)`-cycle of the scheme-theoretic inverse image
`Z.inverseImage f`, i.e. `Hom.flatPullback_integral`. This is well-defined
by Lemma 82.9.1. -/
@[stacks 0EP8]
#check Hom.flatPullback_integral pY pX δ f r hf k Z hZ

/- Definition 82.10.1 (2): In Situation 82.2.1, for a `k`-cycle
`α = ∑ n_i [Z_i]` on `Y`, the flat pullback is the locally finite sum
`f^* α = ∑ n_i f^*[Z_i]`, encoded as `Hom.flatPullback pY pX δ f r hf k α`.
Local finiteness is Lemma 82.9.2. -/
@[stacks 0EP8]
#check Hom.flatPullback pY pX δ f r hf k α

/- Definition 82.10.1 (3): In Situation 82.2.1, the resulting map of abelian
groups is `f^* : Z_k(Y) ⟶ Z_{k+r}(X)`, i.e.
`Hom.flatPullbackHom pY pX δ f r hf k`. -/
@[stacks 0EP8]
#check (Hom.flatPullbackHom pY pX δ f r hf k :
    pY.cycleGroup δ k →+ pX.cycleGroup δ (k + (r : ℤ)))

end
