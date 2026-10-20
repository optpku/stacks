module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.RingTheory.Etale.RegularLocal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular local rings under étale morphisms

This file records invariance of regular-locality for local rings at corresponding
points of an étale morphism.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

/-- An étale morphism preserves regular-locality of the local ring at a point and its image. -/
@[stacks 0AH7]
theorem isRegularLocalRing_stalk_iff {U V : Scheme.{u}} (f : U ⟶ V) [Etale f]
    (u : U) :
    IsRegularLocalRing (U.presheaf.stalk u) ↔
      IsRegularLocalRing (V.presheaf.stalk (f u)) := sorry

end AlgebraicGeometry.Etale
