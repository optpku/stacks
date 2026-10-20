/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent derived tensor products

@stack 0DJE

This file owns closure of pseudo-coherence under the derived tensor product of module complexes.
The bounded statement is expressed with the standard t-structure predicate `IsLE`; pointwise
vanishing of higher homology is a source-facing presentation of that canonical condition.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- Lemma 15.65.16 (1): if `K` and `L` are respectively `n`- and `m`-pseudo-coherent and
bounded above by `a` and `b`, then `K ⊗[R]^L L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 0DJE "pseudo-coherent derived tensor bound"]
theorem IsMPseudoCoherent.tensor
    {K L : DerivedCategory (ModuleCat R)} {n m a b : ℤ}
    (hK : K.IsMPseudoCoherent n) (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m) (hLLE : L.IsLE b) :
    (K ⊗[R]^L L).IsMPseudoCoherent (max (m + a) (n + b)) := sorry
-- Proof strategy: tensor bounded finite-free approximations for `K` and `L`, then use the Tor
-- spectral sequence and the two `IsLE` bounds to obtain the cutoff `max (m + a) (n + b)`.

/-- Lemma 15.65.16 (2): the derived tensor product of two pseudo-coherent module complexes is
pseudo-coherent. -/
@[stacks 0DJE "pseudo-coherent derived tensor product"]
theorem IsPseudoCoherent.tensor
    {K L : DerivedCategory (ModuleCat R)}
    (hK : K.IsPseudoCoherent) (hL : L.IsPseudoCoherent) :
    (K ⊗[R]^L L).IsPseudoCoherent := sorry

-- Proof strategy: choose upper bounds for `K` and `L`, apply the bounded tensor theorem in every
-- pseudo-coherence degree, and use the all-degree characterization of pseudo-coherence.

end CategoryTheory.DerivedCategory
