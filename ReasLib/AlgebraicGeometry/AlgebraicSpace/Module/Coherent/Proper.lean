/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Coherent pushforward along proper morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Ordinary pushforward along a proper morphism to a locally Noetherian
algebraic space preserves coherence. -/
instance pushforward_obj_isCoherent_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] (F : X.Modules) [hF : F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent := sorry

/-- The ordinary pushforward of a coherent module along a proper morphism, as a
coherent module on the target. -/
def coherentPushforwardObj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f] (F : Coh X) : Coh Y :=
  ⟨(pushforward f).obj F.obj,
    pushforward_obj_isCoherent_of_proper f F.obj (hF := F.property)⟩

/-- The underlying module sheaf of `coherentPushforwardObj` is ordinary
pushforward. -/
theorem coherentPushforwardObj_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f] (F : Coh X) :
    (coherentPushforwardObj f F).obj = (pushforward f).obj F.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
