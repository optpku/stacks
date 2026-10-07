module

public import stacks_project.Chap85.Lemma_85_34_1_Comparison
public import stacks_project.Chap85.Lemma_85_34_1_Ringed
import StacksCheckRecall

/-!
# Lemma 85.34.1

For a scheme `S`, an algebraic space `X` over `S`, a simplicial algebraic space
`U` over `S`, and an augmentation `a : U ⟶ X`, the unringed fppf–étale comparison
square of Lemma 85.33.1 upgrades to a commutative square of ringed topoi
`(Sh((Spaces/U)_{fppf,total}), 𝒪_big,total) ⟶ (Sh(U_étale), 𝒪_U)` over
`(Sh((Spaces/X)_fppf), 𝒪_big) ⟶ (Sh(X_étale), 𝒪_X)`. The left vertical arrow
is the Section 85.22/85.21 slice-augmentation; the right vertical arrow is the
Section 85.32 étale augmentation.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Simplicial

/- Lemma 85.34.1
Let S be a scheme. Let X be an algebraic space over S. Let U be a simplicial
algebraic space over S. Let a : U ⟶ X be an augmentation. There is a commutative
diagram of ringed topoi with edges h, a_fppf, a and h₋₁. -/
@[stacks 0DHC] #check AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfEtaleRingedCommSq
