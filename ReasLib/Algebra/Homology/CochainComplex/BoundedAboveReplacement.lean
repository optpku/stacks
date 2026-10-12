/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Predicate
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Horseshoe.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.ForgetBound.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Epi
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Comparison
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Existence

@[expose] public section

/-!
# Bounded-Above Replacements of Cochain Complexes

Convenience import for source-facing predicates, canonical fixed-bound left resolutions,
fixed- and variable-bound dependent additive maps, cutoff-forgetting bridges, horseshoe
constructions, comparisons, and existence results. Each API is owned by its smallest semantic
leaf.
-/
