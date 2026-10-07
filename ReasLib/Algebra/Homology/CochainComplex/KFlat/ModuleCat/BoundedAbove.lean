module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above K-flat complexes of modules

@stack 064K

This file specializes the categorical bounded-above K-flatness theorem to cochain complexes of
modules over a commutative ring.  The specialization discharges the exact-countable-coproduct
hypotheses supplied by `ModuleCat`.
-/

@[expose] public section

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Lemma 15.59.7 (064K), in the commutative-ring setting: a bounded-above complex of flat
modules is K-flat. -/
@[stacks 064K "bounded-above complexes of flat modules are K-flat"]
theorem isKFlat_of_boundedAbove_of_flat
    (P : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) P)
    (hFlat : P.IsTermwiseFlat) :
    P.IsKFlat := sorry

end CochainComplex
