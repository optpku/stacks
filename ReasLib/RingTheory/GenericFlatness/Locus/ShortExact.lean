/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.FinitePresentation.Exact
public import ReasLib.RingTheory.GenericFlatness.Localization.Away
public import ReasLib.RingTheory.GenericFlatness.Locus

/-!
# Generic-flatness loci in short exact sequences

The condition-level closure statement and the induced locus inclusion are kept
separate, so applications can use either layer without replaying the basic-open
refinement argument.
-/

@[expose] public section

universe u v

namespace GenericFlatness

/- API design for 051W: the condition-level theorem is the algebraic closure rule and the
locus inclusion is its topological consumer.  Keeping both avoids forcing downstream proofs to
unpack the union-of-basic-opens definition when they already have a fixed localization witness. -/

namespace LocalizationCondition

/-- Lemma 10.118.4 (1) (Tag 051W): in a short exact sequence of modules, generic-flatness
localization conditions for the two outer terms imply the condition for the middle term at the
same parameter. -/
@[stacks 051W "(1), generic-flatness localization condition in a short exact sequence"]
theorem ofShortExact
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : CategoryTheory.ShortComplex (ModuleCat.{max u v} S)}
    (f : R) (hT : T.ShortExact)
    (h1 : LocalizationCondition R S T.X₁ f)
    (h3 : LocalizationCondition R S T.X₃ f) :
    LocalizationCondition R S T.X₂ f := sorry

end LocalizationCondition

namespace ShortExact

/-- In a short exact sequence, the intersection of the good loci of the outer terms is contained
in the good locus of the middle term. -/
@[stacks 051W "(2), generic-flatness locus in a short exact sequence"]
theorem goodLocus_inter_subset
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : CategoryTheory.ShortComplex (ModuleCat.{max u v} S)}
    (hT : T.ShortExact) :
    goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂ := sorry

end ShortExact
end GenericFlatness
