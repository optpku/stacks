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
@stack 064K
@stack 0A60
@stack 0E1U
-/

@[expose] public section

universe u v

namespace HomologicalComplex

variable {ι : Type v} {c : ComplexShape ι}

section Ring

variable {R : Type u} [Ring R]

/-- Stacks `0A60`: a module-valued homological complex is termwise finite projective when every component is a
finite projective module. -/
@[stacks 0A60 "termwise finite-projective complexes"]
def IsTermwiseFiniteProjective
    (K : HomologicalComplex (ModuleCat R) c) : Prop :=
  ∀ i : ι, Module.FiniteProjective R (K.X i)

namespace IsTermwiseFiniteProjective

variable {K : HomologicalComplex (ModuleCat R) c}

/-- Stacks `0A60`: every component of a termwise finite-projective complex is finite. -/
@[stacks 0A60 "finite components of termwise finite-projective complexes"]
theorem finite (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    Module.Finite R (K.X i) := sorry
/- Proof strategy: specialize the defining degreewise predicate and project
`Module.FiniteProjective.finite` at `K.X i`. -/

/-- Stacks `0A60`: every component of a termwise finite-projective complex is projective. -/
@[stacks 0A60 "projective components of termwise finite-projective complexes"]
theorem projective (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    Module.Projective R (K.X i) := sorry
/- Proof strategy: specialize `hK` at `i` and project
`Module.FiniteProjective.projective`. -/

/-- Stacks `0A60`: every component of a termwise finite-projective complex is a projective object of the
module category. -/
@[stacks 0A60 "categorically projective components of termwise finite-projective complexes"]
theorem projectiveObject (hK : K.IsTermwiseFiniteProjective) (i : ι) :
    CategoryTheory.Projective (K.X i) := sorry
/- Proof strategy: use `hK.projective i` and the canonical
`ModuleCat.projective_of_categoryTheory_projective` instance. -/

/-- Stacks `058R`: a termwise finite-projective complex is termwise finitely presented. -/
@[stacks 058R "finite-projective complexes are termwise finitely presented"]
theorem termwiseFinitePresentation (hK : K.IsTermwiseFiniteProjective) :
    K.IsTermwiseFinitePresentation := sorry
/- Proof strategy: specialize `hK` in each degree and apply
`Module.FiniteProjective.finitePresentation`. -/

/-- Stacks `0E1U`: a termwise finite-free complex is termwise finite projective. -/
@[stacks 0E1U "finite-free complexes are termwise finite-projective"]
theorem of_finiteFree (hK : K.IsTermwiseFiniteFree) :
    K.IsTermwiseFiniteProjective := sorry
/- Proof strategy: apply `Module.FiniteFree.finiteProjective` degreewise through the
termwise finite-free predicate. -/

end IsTermwiseFiniteProjective

/-- Stacks `0A60`: termwise finite projectivity unfolds degreewise. -/
@[stacks 0A60 "degreewise termwise finite-projectivity criterion"]
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

/-- Stacks `064K`: a termwise finite-projective complex is termwise flat. -/
@[stacks 064K "finite-projective complexes are termwise flat"]
theorem termwiseFlat (hK : K.IsTermwiseFiniteProjective) :
    K.IsTermwiseFlat := sorry
/- Proof strategy: use `Module.FiniteProjective.flat` on each component and unfold
`HomologicalComplex.IsTermwiseFlat`. -/

end IsTermwiseFiniteProjective

end CommRing

end HomologicalComplex

namespace ChainComplex

variable {R : Type u} [Ring R]

/-- Stacks `0A60`: the chain-complex specialization of termwise finite projectivity. -/
@[stacks 0A60 "chain-complex termwise finite projectivity"]
abbrev IsTermwiseFiniteProjective
    (K : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteProjective K

end ChainComplex

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- Stacks `0A60`: the integer cochain-complex specialization of termwise finite projectivity. -/
@[stacks 0A60 "cochain-complex termwise finite projectivity"]
abbrev IsTermwiseFiniteProjective
    (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteProjective K

end CochainComplex
