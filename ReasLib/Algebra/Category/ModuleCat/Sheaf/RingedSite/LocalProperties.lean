/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalGeneration

/-!
# Local Properties of Sheaves of Modules

Convenience import for Mathlib's local-freeness, finite-type,
quasi-coherence, and finite-presentation predicates together with the missing
finite-local-freeness, fixed-generation, and coherence refinements.  Rank is
kept in its own leaf because it is not one of the properties defined here.
-/
@[expose] public section

