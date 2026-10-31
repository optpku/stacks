/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FinitePresentation
public import ReasLib.RingTheory.Finiteness.Projective
public import ReasLib.RingTheory.Finiteness.Projective.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise finite-projective complexes

This leaf owns the shape-independent finite-projective condition for module-valued homological
complexes.  It is a proposition with explicit proof arguments: termwise finite projectivity is a
property of a complex, not additional data that typeclass search should reconstruct.
-/

@[expose] public section

universe u v

namespace HomologicalComplex

variable {ι : Type v} {c : ComplexShape ι}

section Ring

variable {R : Type u} [Ring R]

/-- Library infrastructure: a module-valued homological complex is termwise finite projective when every component is a
finite projective module. -/
def IsTermwiseFiniteProjective
    (K : HomologicalComplex (ModuleCat R) c) : Prop :=
  ∀ i : ι, Module.FiniteProjective R (K.X i)

namespace IsTermwiseFiniteProjective

variable {K : HomologicalComplex (ModuleCat R) c}

/-- Library infrastructure: every component of a termwise finite-projective complex is finite. -/
theorem finite (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    Module.Finite R (K.X i) := sorry
/- Proof strategy: specialize the defining degreewise predicate and project
`Module.FiniteProjective.finite` at `K.X i`. -/

/-- Library infrastructure: every component of a termwise finite-projective complex is projective. -/
theorem projective (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    Module.Projective R (K.X i) := sorry
/- Proof strategy: specialize `hK` at `i` and project
`Module.FiniteProjective.projective`. -/

/-- Library infrastructure: every component of a termwise finite-projective complex is a projective object of the
module category. -/
theorem projectiveObject (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    CategoryTheory.Projective (K.X i) := sorry
/- Proof strategy: use `hK.projective i` and the canonical
`ModuleCat.projective_of_categoryTheory_projective` instance. -/

/-- Library infrastructure: a termwise finite-projective complex is termwise finitely presented.
Over a commutative ring this follows degreewise from the forward implication of Stacks `058R`.
The statement here holds more generally over an arbitrary ring. -/
theorem termwiseFinitePresentation (hK : K.IsTermwiseFiniteProjective) :
    K.IsTermwiseFinitePresentation := sorry
/- Proof strategy: specialize `hK` in each degree and apply
`Module.FiniteProjective.finitePresentation`. -/

/-- Library infrastructure: a termwise finite-free complex is termwise finite projective. -/
theorem of_finiteFree (hK : K.IsTermwiseFiniteFree) :
    K.IsTermwiseFiniteProjective := sorry
/- Proof strategy: apply `Module.FiniteFree.finiteProjective` degreewise through the
termwise finite-free predicate. -/

end IsTermwiseFiniteProjective

/-- Library infrastructure: termwise finite projectivity unfolds degreewise. -/
theorem isTermwiseFiniteProjective_iff
    (K : HomologicalComplex (ModuleCat R) c) :
    K.IsTermwiseFiniteProjective ↔
      ∀ i : ι, Module.FiniteProjective R (K.X i) := sorry
/- Proof strategy: unfold `HomologicalComplex.IsTermwiseFiniteProjective` in both directions. -/

end Ring

section CommRing

variable {R : Type u} [CommRing R]
variable {K : HomologicalComplex (ModuleCat R) c}

namespace IsTermwiseFiniteProjective

/-- Library infrastructure: a termwise finite-projective complex is termwise flat.
Stacks `064K` concerns K-flatness of bounded-above complexes of flat modules and is not this
degreewise statement. -/
theorem termwiseFlat (hK : K.IsTermwiseFiniteProjective) :
    K.IsTermwiseFlat := sorry
/- Proof strategy: use `Module.FiniteProjective.flat` on each component and unfold
`HomologicalComplex.IsTermwiseFlat`. -/

end IsTermwiseFiniteProjective

end CommRing

end HomologicalComplex

namespace ChainComplex

variable {R : Type u} [Ring R]

/-- Library infrastructure: the chain-complex specialization of termwise finite projectivity. -/
abbrev IsTermwiseFiniteProjective
    (K : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteProjective K

end ChainComplex

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- Library infrastructure: the integer cochain-complex specialization of termwise finite projectivity. -/
abbrev IsTermwiseFiniteProjective
    (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteProjective K

end CochainComplex
