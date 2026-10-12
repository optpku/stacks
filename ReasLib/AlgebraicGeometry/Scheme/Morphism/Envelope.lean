/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed

/-!
# Envelopes of Schemes

This module defines envelope morphisms of schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {Y X : Scheme.{u}}

/-- An envelope is a proper, completely decomposed morphism of schemes. -/
class IsEnvelope (f : Y ⟶ X) : Prop extends IsProper f, Scheme.Hom.CompletelyDecomposed f

namespace IsEnvelope

/-- A proper, completely decomposed morphism of schemes is an envelope. -/
instance instOfProperties (f : Y ⟶ X) [IsProper f] [Scheme.Hom.CompletelyDecomposed f] :
    IsEnvelope f := sorry

/-- An envelope satisfies properness and complete decomposition. -/
theorem spec (f : Y ⟶ X) [IsEnvelope f] :
    IsProper f ∧ Scheme.Hom.CompletelyDecomposed f := sorry

end IsEnvelope

/-- Envelopehood is equivalent to properness together with complete decomposition. -/
theorem isEnvelope_iff (f : Y ⟶ X) :
    IsEnvelope f ↔ IsProper f ∧ Scheme.Hom.CompletelyDecomposed f := sorry

end

end AlgebraicGeometry
