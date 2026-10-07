module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Tensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

/-!
# Lemma 15.65.16: pseudo-coherence and derived tensor products

The reusable tensor-closure theorems are owned by
`CategoryTheory.DerivedCategory.IsMPseudoCoherent.tensor` and
`CategoryTheory.DerivedCategory.IsPseudoCoherent.tensor`.  The standard t-structure condition
`K.IsLE a` is the canonical formalization of vanishing of `H^i(K)` for `i > a`.

@stack 0DJE
-/

/- Lemma 15.65.16 (1), tag `0DJE`: bounded pseudo-coherence of a derived tensor product. -/
@[stacks 0DJE "(1), bounded pseudo-coherence of a derived tensor product"]
#check fun {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat R)} {n m a b : ℤ}
    (hK : K.IsMPseudoCoherent n) (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m) (hLLE : L.IsLE b) ↦
  (CategoryTheory.DerivedCategory.IsMPseudoCoherent.tensor hK hKLE hL hLLE :
    (K ⊗[R]^L L).IsMPseudoCoherent (max (m + a) (n + b)))

/- Lemma 15.65.16 (2), tag `0DJE`: pseudo-coherence is closed under derived tensor products. -/
@[stacks 0DJE "(2), pseudo-coherence of a derived tensor product"]
#check fun {R : Type u} [CommRing R] {K L : DerivedCategory (ModuleCat R)}
    (hK : K.IsPseudoCoherent) (hL : L.IsPseudoCoherent) ↦
  (CategoryTheory.DerivedCategory.IsPseudoCoherent.tensor hK hL :
    (K ⊗[R]^L L).IsPseudoCoherent)

#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.tensor
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.tensor
