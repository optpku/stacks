module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Kollar

/-!
# Normal local rings and Kollár's exceptional branch

This leaf isolates the normal-domain exclusion used alongside Kollár's local-ring
criterion.  The normality hypothesis is expressed by the canonical domain and
integral-closedness typeclasses, so the result applies independently of any
chapter-specific presentation of normality.
-/

@[expose] public section

universe u

namespace IsLocalRing.Kollar.Normal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A positive-dimensional Noetherian normal local domain has no Kollár exceptional finite
extension.  Here normality is represented by the canonical `IsDomain` and `IsIntegrallyClosed`
typeclasses, while the exceptional branch is the neutral owner `HasExceptionalExtension R`. -/
@[stacks 0BHZ "positive-dimensional normal local domain excludes exceptional extensions"]
theorem notExceptional_of_krullDim_ne_zero [IsDomain R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≠ 0) :
    ¬ IsLocalRing.Kollar.HasExceptionalExtension R := sorry

end IsLocalRing.Kollar.Normal
