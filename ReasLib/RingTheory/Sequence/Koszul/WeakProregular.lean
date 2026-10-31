/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.EventualZero
public import ReasLib.RingTheory.Sequence.Koszul.Power
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly proregular finite families

Weak proregularity is expressed on the canonical powered Koszul chain tower. Since these are
chain complexes, the source's negative cohomological degrees correspond to positive homological
degrees here.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u v

namespace KoszulComplex

variable {R : Type u} [CommRing R]

/-- A finite family is weakly proregular when the inverse system of homology of its powered
Koszul complexes is eventually zero in every positive degree. -/
@[stacks 0H1E "weakly proregular finite family"]
def IsWeaklyProregular {ι : Type v} [Finite ι] (f : ι → R) : Prop :=
  ∀ p : ℕ, 0 < p →
    PreorderInverseSystem.Transition.EventuallyZero
      (powerSystem f ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) p)

namespace IsWeaklyProregular

/-- Source-shaped weak proregularity: from every powered stage there is one strictly later
transition which vanishes on homology simultaneously in every positive degree. -/
@[stacks 0H1E "simultaneous transition form of weak proregularity"]
def AtOnce {ι : Type v} [Finite ι] (f : ι → R) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
    ∀ p : ℕ, 0 < p →
      HomologicalComplex.homologyMap
        (PreorderInverseSystem.transitionMap (powerSystem f) hnm.le) p = 0

end IsWeaklyProregular

/-- For a finite Koszul complex, homologywise eventual vanishing is equivalent to choosing one
later transition which vanishes in all positive degrees simultaneously. -/
theorem isWeaklyProregular_iff_atOnce {ι : Type v} [Finite ι] (f : ι → R) :
    IsWeaklyProregular f ↔ IsWeaklyProregular.AtOnce f := sorry

/-- The finite-amplitude bridge used by `isWeaklyProregular_iff_atOnce`: degreewise eventual
vanishing can be uniformized over the positive degrees that remain after the powered Koszul
complexes' high-degree homology has vanished. -/
@[stacks 0H1E "finite-amplitude uniformization of weak proregularity"]
theorem isWeaklyProregular_uniformized {ι : Type v} [Finite ι] (f : ι → R)
    (h : IsWeaklyProregular f) : IsWeaklyProregular.AtOnce f := sorry

/-- Positive-degree homology transitions of a weakly proregular family are eventually zero. -/
theorem IsWeaklyProregular.eventuallyZero {ι : Type v} [Finite ι] {f : ι → R}
    (h : IsWeaklyProregular f) (p : ℕ) (hp : 0 < p) :
    PreorderInverseSystem.Transition.EventuallyZero
      (powerSystem f ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) p) :=
  h p hp

end KoszulComplex
