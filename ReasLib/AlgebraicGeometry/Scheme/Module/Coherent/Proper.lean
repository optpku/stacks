/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent

/-!
# Coherent modules and proper morphisms

Proper morphisms preserve coherence under ordinary pushforward over locally Noetherian schemes.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Ordinary pushforward along a proper morphism to a locally Noetherian scheme preserves
coherence. -/
instance pushforward_obj_isCoherent_of_proper
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
