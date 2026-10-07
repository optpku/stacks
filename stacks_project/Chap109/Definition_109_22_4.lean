module

public import stacks_project.Chap109.Lemma_109_22_5_Substack
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Definition 109.22.4 (1): we denote ℳ̄ and name it the moduli stack of
stable curves the algebraic stack 𝒞urves^{stable} parametrizing stable
families of curves introduced in Lemma 109.22.3. -/
@[stacks 0E77] #check stable

/- Definition 109.22.4 (2): for g ≥ 2 we denote ℳ̄_g and name it the moduli
stack of stable curves of genus g the algebraic stack introduced in
Lemma 109.22.5. -/
@[stacks 0E77] #check stableOfGenus
