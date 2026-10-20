module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.LocalRing.Kollar

/-!
# Kollar's local-ring criterion

This leaf owns the four-way local-ring alternative.  The exceptional branch is
the predicate from `ReasLib.RingTheory.LocalRing.Kollar`, while this file keeps
the criterion itself independent of chapter-facing proofs and imports.
-/

@[expose] public section

universe u

namespace IsLocalRing.Kollar

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Kollar's local-ring criterion: exactly one of the Artinian,
regular-dimension-one, depth-at-least-two, and exceptional-extension alternatives holds. -/
@[stacks 0BHZ "Kollar local-ring criterion"]
theorem exactlyOne :
    Xor' (IsArtinianRing R)
      (Xor' (IsRegularLocalRing R ∧ ringKrullDim R = 1)
        (Xor' ((2 : WithTop ℕ) ≤ moduleDepth R R)
          (HasExceptionalExtension R))) := sorry

/-- Depth at least two excludes Kollar's exceptional finite-extension alternative. -/
@[stacks 0BHZ "depth excludes Kollar exceptional extensions"]
theorem notExceptionalOfDepthTwo
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R) :
    ¬ HasExceptionalExtension R := sorry

end IsLocalRing.Kollar
