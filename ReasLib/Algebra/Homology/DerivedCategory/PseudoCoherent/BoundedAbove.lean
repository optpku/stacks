/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above pseudo-coherence criteria

This leaf contains the absolute cochain-complex criterion used by the relative
presentationwise version.

@stack 064Y
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.CochainComplex

/-- A bounded-above cochain complex is `m`-pseudo-coherent when its degree `i` term is
`(m - i)`-pseudo-coherent for every integer `i`. -/
@[stacks 064Y "m-pseudo-coherence from bounded-above terms"]
theorem isMPseudoCoherent_of_boundedAbove_of_termwise
    {S : Type u} [Ring S] (K : CochainComplex (ModuleCat S) ℤ) (m : ℤ)
    (h_bounded : CochainComplex.minus (ModuleCat S) K)
    (h_term : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    K.IsMPseudoCoherent m := sorry

end CategoryTheory.CochainComplex
