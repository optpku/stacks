module

public import ReasLib.RingTheory.CotangentComplex.DirectLimit
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 92.3.4: For a directed system of ring maps, the canonical comparison from
the direct limit of their cotangent complexes to the cotangent complex of the
induced direct-limit ring map is an isomorphism. -/
@[stacks 08S9] #check (Algebra.CotangentComplex.DirectLimit.comparison_isIso :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {R S : I → Type u}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (ρ : ∀ i j, i ≤ j → R i →+* R j)
    (σ : ∀ i j, i ≤ j → S i →+* S j)
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))),
    CategoryTheory.IsIso (Algebra.CotangentComplex.DirectLimit.comparison ρ σ hcomm))
