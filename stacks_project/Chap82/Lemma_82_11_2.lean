module

public import stacks_project.Chap82.Lemma_82_11_2_PushPull
public import stacks_project.Chap82.Lemma_82_11_2_RelativeDimension
import StacksCheckRecall

/-!
# Finite locally free morphisms of algebraic spaces and cycles

In Situation 82.2.1, a finite locally free morphism of degree `d` between good
algebraic spaces over `B` is proper and flat of relative dimension `0`, and
push-pull of `k`-cycles is multiplication by `d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f]

/- A finite locally free morphism of algebraic spaces is proper. -/
#check (inferInstance : Proper f)

/- A finite locally free morphism of algebraic spaces is flat. -/
#check (inferInstance : Flat f)

end

/- Lemma 82.11.2 (1): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a finite locally free morphism of degree `d`. Then `f` is of
relative dimension `0`. -/
@[stacks 0EPE] #check FiniteLocallyFree.instRelativeDimension_zero

/- Lemma 82.11.2 (2): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a finite locally free morphism of degree `d`. Then
`f_* (f^* α) = d • α` for every `α ∈ Z_k(Y)`. -/
@[stacks 0EPE] #check Hom.properPushforward_flatPullback_nsmul
