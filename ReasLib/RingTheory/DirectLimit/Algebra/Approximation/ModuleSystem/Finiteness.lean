/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness at the limit of a directed module system

The base-change fields of `ModuleSystem` turn a finitely presented stage into
finitely presented limiting ring and module data.  The per-stage lemmas are
the fine-grained API; the `hasFinitePresentation` consequences provide the
common source-facing package.
-/

@[expose] public section

universe u v x

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Upgrade finite stage modules to finitely presented stage modules when the
stage maps are finitely presented and the target stages are Noetherian. -/
@[stacks 02JO "finite-presentation directed module system"]
theorem hasFinitePresentation_of_finite (A : ModuleSystem f M)
    (hmap : ∀ i, (A.map i).FinitePresentation)
    (hnoetherian : ∀ i, IsNoetherianRing (A.target i))
    (hfinite : A.hasFinite) :
    A.hasFinitePresentation := sorry

/-- A finitely presented stage module gives a finitely presented limiting
module through the final base-change equivalence. -/
@[stacks 02JO "directed module-system limit finiteness"]
theorem finalModule_finitePresentation_at (A : ModuleSystem f M) (i : A.index)
    (hstageModule : _root_.Module.FinitePresentation (A.target i) (A.moduleStage i)) :
    _root_.Module.FinitePresentation S M := sorry

/-- The stage-module component of `hasFinitePresentation` gives a finitely
presented limiting module.  This convenience form asks only for the module
component; callers that also need the map conclusion should use
`final_finitePresentation`. -/
@[stacks 02JO "directed module-system limit finiteness"]
theorem finalModule_finitePresentation_of_modules (A : ModuleSystem f M)
    (hmodule : ∀ i, _root_.Module.FinitePresentation (A.target i) (A.moduleStage i)) :
    _root_.Module.FinitePresentation S M := sorry

/-- A finite-presentation directed module system automatically supplies both
global finite-presentation assumptions used in the flatness theorem. -/
@[stacks 02JO "directed module-system limit finiteness"]
theorem final_finitePresentation (A : ModuleSystem f M)
    (hfinitePresentation : A.hasFinitePresentation) :
    f.FinitePresentation ∧ _root_.Module.FinitePresentation S M := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
