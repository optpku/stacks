module

import StacksCheckRecall
public import stacks_project.Chap72.«72_12_5_1_Galois»

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CommRingCat

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable (X : AlgebraicSpace (Spec (of k)))

/- 72.12.5.1: Let k be a field, let K/k be a (possibly infinite) Galois extension, and let X
be an algebraic space over k. Then Spec(σ) ∘ Spec(τ) = Spec(τ ∘ σ), so Gal(K/k)ᵐᵒᵖ acts on
Spec K over Spec k. The product X_K = Spec K ×_{Spec k} X induces a canonical action
Gal(K/k)ᵐᵒᵖ × X_K ⟶ X_K. -/
@[stacks 0A14] #check
  (AlgebraicSpace.FieldExtension.Galois.opAutHom k K X :
    (Gal(K/k))ᵐᵒᵖ →* Aut (AlgebraicSpace.FieldExtension.baseChange k K X))
