/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Bounded

/-!
# Homology criteria for relative pseudo-coherence

@stack 0678

This leaf provides derived bounded-above criteria without imposing a
Noetherian hypothesis on the base algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- Lemma 15.82.10 (1): a bounded-above derived complex is `m`-pseudo-coherent relative to `R`
when its cohomology in degree `i` is `(m - i)`-pseudo-coherent relative to `R`. -/
@[stacks 0678 "(1), relative m-pseudo-coherence from homology"]
theorem boundedAbove_isMPseudoCoherentRelativeTo_of_homology
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory.Minus (ModuleCat A)) (m : ℤ)
    (h_homology : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K.obj).IsMPseudoCoherentRelativeTo R
        (m - i)) :
    K.obj.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.10 (2): a bounded-above derived complex is pseudo-coherent relative to `R` when
all of its cohomology modules are pseudo-coherent relative to `R`. -/
@[stacks 0678 "(2), relative pseudo-coherence from homology"]
theorem boundedAbove_isPseudoCoherentRelativeTo_of_homology
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory.Minus (ModuleCat A))
    (h_homology : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K.obj).IsPseudoCoherentRelativeTo R) :
    K.obj.IsPseudoCoherentRelativeTo R := sorry

end CategoryTheory
