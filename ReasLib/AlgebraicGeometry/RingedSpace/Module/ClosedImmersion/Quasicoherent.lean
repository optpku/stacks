module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalCokernel
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Coproduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local cokernel presentations under a closed immersion

The reusable theorem isolates the actual proof inputs: a closed embedding, colimit preservation,
and quasi-coherence of the pushed-forward unit. The closed-immersion specialization supplies
these inputs through canonical instances. No theorem here claims that arbitrary pushforwards are
quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedEmbedding

variable {X Z : RingedSpace.{u}}

/-- A quasi-coherent module pushes forward to a cover-local cokernel of quasi-coherent modules
when the closed pushforward preserves colimits and sends the unit to a quasi-coherent module. -/
@[stacks 01C3 "closed embedding core"]
theorem mem_localCokernels
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    [PreservesColimitsOfSize (pushforward i)]
    [((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).IsQuasicoherent]
    (F : Z.Modules) [F.IsQuasicoherent] :
    SheafOfModules.RingedSite.localCokernels.quasicoherent ((pushforward i).obj F) := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedEmbedding

namespace AlgebraicGeometry.RingedSpace.IsClosedImmersion

variable {X Z : RingedSpace.{u}}

/-- The pushed-forward source structure module is quasicoherent as an ambient module. This
instance bridges the ringed-space pushforward notation to the generic locally-surjective
structure-module quotient API. -/
@[stacks 01C3 "pushed-forward structure module", instance]
instance pushforwardUnit_isQuasicoherent
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).IsQuasicoherent := sorry

/-- Lemma 17.13.2 (01C3): the pushforward of a quasi-coherent module sheaf along a closed
immersion is locally a cokernel of a morphism between quasi-coherent module sheaves. -/
@[stacks 01C3]
theorem pushforward_mem_localCokernels
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (F : Z.Modules) [F.IsQuasicoherent] :
    SheafOfModules.RingedSite.localCokernels.quasicoherent ((pushforward i).obj F) := sorry

variable (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]

#synth ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).IsQuasicoherent
#synth PreservesColimitsOfSize (pushforward i)

end AlgebraicGeometry.RingedSpace.IsClosedImmersion
