module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.InternalHom

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)
variable (h_closed : Topology.IsClosedEmbedding i.hom.base)
variable [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]

#check
  (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction i h_closed :
    RingedSpace.Hom.pushforward i ⊣
      RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf i h_closed)
