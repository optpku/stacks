/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Module.FinitePresentation.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of pseudo-coherent derived modules

The highest potentially nonzero homology objects of an `m`-pseudo-coherent derived module are
finite, with finite presentation one degree above the approximation bound.  The canonical API is
stated using the derived t-structure; cochain-complex companions preserve the explicit vanishing
form used in source calculations.

@stack 064S
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [Ring R]
variable {K : DerivedCategory (ModuleCat R)} {m : ℤ}

/-- Lemma 15.65.3 (1): the top homology of an `m`-pseudo-coherent object in `D(R)_{≤ m}` is
finite. -/
@[stacks 064S "(1)"]
theorem topHomology_finite (hK : K.IsMPseudoCoherent m) (hLE : K.IsLE m) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat R) m).obj K) := sorry

/-- Lemma 15.65.3 (2): degree `m + 1` homology of an `m`-pseudo-coherent object in
`D(R)_{≤ m + 1}` is finitely presented. -/
@[stacks 064S "(2)"]
theorem nextHomology_finitePresentation
    (hK : K.IsMPseudoCoherent m) (hLE : K.IsLE (m + 1)) :
    Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (m + 1)).obj K) := sorry

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.CochainComplex.IsMPseudoCoherent

variable {R : Type u} [Ring R]
variable {K : CochainComplex (ModuleCat R) ℤ} {m : ℤ}

/-- The top cochain homology is finite when all homology above the pseudo-coherence bound
vanishes. -/
@[stacks 064S "(1), cochain form"]
theorem topHomology_finite (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i)) :
    Module.Finite R (K.homology m) := sorry

/-- The next cochain homology is finitely presented when all homology above that degree
vanishes. -/
@[stacks 064S "(2), cochain form"]
theorem nextHomology_finitePresentation (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) :
    Module.FinitePresentation R (K.homology (m + 1)) := sorry

end CategoryTheory.CochainComplex.IsMPseudoCoherent
