/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Predicate
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Horseshoe.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.ForgetBound.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Mono
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Comparison
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Existence

@[expose] public section

/-!
# Bounded-Below Replacements of Cochain Complexes

Convenience import for source-facing predicates, canonical fixed-bound right resolutions,
fixed- and variable-bound dependent additive maps, cutoff-forgetting bridges, horseshoe
constructions, comparisons, and existence results. Each API is owned by its smallest semantic
leaf.
-/
