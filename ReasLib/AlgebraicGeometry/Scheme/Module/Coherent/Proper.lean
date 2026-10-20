/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent

/-!
# Coherent modules and proper morphisms

Proper morphisms preserve coherence under ordinary pushforward over locally Noetherian schemes.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Ordinary pushforward along a proper morphism to a locally Noetherian scheme preserves
coherence. -/
instance pushforward_obj_isCoherent_of_proper
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent := sorry

/-- The ordinary pushforward of a coherent module along a proper morphism, as a coherent module
on the target. -/
def coherentPushforwardObj [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : RingedSpace.Coh X.toRingedSpace) : RingedSpace.Coh Y.toRingedSpace :=
  ⟨(pushforward f).obj F.obj, @pushforward_obj_isCoherent_of_proper X Y f _ _ F.obj F.property⟩

/-- The underlying module sheaf of `coherentPushforwardObj` is ordinary pushforward. -/
theorem coherentPushforwardObj_obj [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : RingedSpace.Coh X.toRingedSpace) :
    (coherentPushforwardObj f F).obj = (pushforward f).obj F.obj :=
  rfl

end AlgebraicGeometry.Scheme.Modules
