module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above cohomology criteria

This leaf owns the homological form of the bounded-above pseudo-coherence criterion.  The input is
the canonical object of `DerivedCategory.Minus`; no chapter-specific bounded-category alias or
selected derived presentation is part of the public API.

@stack 066B
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [Ring R]

/-- Lemma 15.65.10 (1): degreewise `(m - i)`-pseudo-coherence of the cohomology of a bounded-above
derived object implies `m`-pseudo-coherence of that object. -/
@[stacks 066B "(1), bounded-above m-pseudo-coherence from cohomology"]
theorem IsMPseudoCoherent.of_boundedAbove_homology
    (K : DerivedCategory.Minus (ModuleCat R)) (m : ℤ)
    (hH : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj).IsMPseudoCoherent (m - i)) :
    K.obj.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.10 (2): pseudo-coherence of every cohomology module of a bounded-above derived
object implies pseudo-coherence of that object. -/
@[stacks 066B "(2), bounded-above pseudo-coherence from cohomology"]
theorem IsPseudoCoherent.of_boundedAbove_homology
    (K : DerivedCategory.Minus (ModuleCat R))
    (hH : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj).IsPseudoCoherent) :
    K.obj.IsPseudoCoherent := sorry

end CategoryTheory.DerivedCategory

end
