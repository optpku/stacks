module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 17.13.3 (01C4): a closed embedding with locally surjective structure-sheaf map
preserves and reflects finite type under module pushforward. -/
@[stacks 01C4]
#check fun {X Z : RingedSpace.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (F : Z.Modules) ↦
  RingedSpace.Hom.ModulePushforward.ClosedEmbedding.isFiniteType_iff i hi F

/- Reflection uses only the induced-topology hypothesis; the closed-immersion class remains a
convenient stronger specialization. -/
#check @RingedSpace.Hom.ModulePushforward.Inducing.of_pushforward_isFiniteType
#check @RingedSpace.IsClosedImmersion.pushforward_isFiniteType_iff
#check @RingedSpace.Hom.stalkMap_surjective_of_isInducing
