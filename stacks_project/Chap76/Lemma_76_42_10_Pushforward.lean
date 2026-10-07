module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion

/-!
# Coherent pushforward along proper morphisms of algebraic spaces

Ordinary pushforward of a coherent module along a proper morphism to a
locally Noetherian algebraic space remains coherent, and is recorded as an
object of `Coh`.
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
    [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent :=
  sorry

/-- The ordinary pushforward of a coherent module along a proper morphism, as a
coherent module on the target. -/
def coherentPushforwardObj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f] (F : Coh X) : Coh Y :=
  ⟨(pushforward f).obj F.obj,
    @pushforward_obj_isCoherent_of_proper S X Y f _ _ F.obj F.property⟩

/-- The underlying module sheaf of `coherentPushforwardObj` is ordinary
pushforward. -/
theorem coherentPushforwardObj_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f] (F : Coh X) :
    (coherentPushforwardObj f F).obj = (pushforward f).obj F.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
