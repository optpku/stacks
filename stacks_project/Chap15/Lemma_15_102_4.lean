/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext.PseudoCoherent

/-!
# Lemma 15.102.4

@stack 0DYI
-/

@[expose] public section

open CategoryTheory
open Ideal.PowerSubmodule
open CategoryTheory.DerivedCategory.IdealPower.ExtImage

noncomputable section

universe u

/-
Lemma 15.102.4 (0DYI): let `A` be a Noetherian ring, let `I` be an ideal of `A`, let
`K ∈ D(A)` be pseudo-coherent, and let `M` be a finite `A`-module.  For every `p : ℤ`
there is a cutoff `c` such that, whenever `n ≥ c`, the image of

`Ext^p_A(K, I ^ n M) ⟶ Ext^p_A(K, M)`

is contained in `I ^ (n - c) Ext^p_A(K, M)`.

The ReasLib owner separates the restriction map, the pointwise image bound, and its eventual
Noetherian producer.  This file is only the exact source-facing recall boundary.
-/

@[stacks 0DYI "derived Ext map from an adic stage"]
#check @restriction
@[stacks 0DYI "pointwise adic image bound for derived Ext"]
#check @ImageBound
@[stacks 0DYI "eventual adic image bound for derived Ext"]
#check @EventuallyBounded
@[stacks 0DYI "pseudo-coherent derived Ext image bound"]
#check @eventuallyBounded_of_isPseudoCoherent

section SourceStatement

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) {K : DerivedCategory (ModuleCat A)}
variable (hK : K.IsPseudoCoherent) (M : ModuleCat A) [Module.Finite A M] (p : ℤ)

@[stacks 0DYI "Lemma 15.102.4"]
#check (eventuallyBounded_of_isPseudoCoherent I hK M p :
  ∃ c : ℕ, ∀ n, c ≤ n →
    LinearMap.range (restriction I K M p n).hom ≤
      stage I ((DerivedCategory.Ext.moduleFunctor K p).obj M) (n - c))

end SourceStatement
