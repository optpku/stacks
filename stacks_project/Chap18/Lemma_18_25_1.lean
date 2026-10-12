/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 18.25.1

The generic kernel-annihilation predicate and all closed-immersion consequences are owned in
ReasLib.  The source's two hypotheses remain separate, matching its deliberate choice not to
define a bundled notion of closed immersion for ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismOfTopoiIn
open RingedSite.Hom.ModulePushforward

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom.ModulePushforward

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vX, z}]
variable (f : X.Hom Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type z) Y.siteTopology X.siteTopology)]
variable [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap]

/- Lemma 18.25.1 (1) (08M3): under the closed-immersion and epic structure-map hypotheses,
module pushforward is exact. -/
@[stacks 08M3 "(1)"]
#check
  (exact_of_closedImmersion f :
    exactFunctor
      (ModuleCat.{z} X) (ModuleCat.{z} Y)
      f.modulePushforward.{z})

/- Lemma 18.25.1 (2) (08M3): under the same hypotheses, module pushforward is fully
faithful. -/
@[stacks 08M3 "(2)"]
#check
  (fullyFaithful_of_closedImmersion_of_epi f :
    f.modulePushforward.{z}.FullyFaithful)

variable (G : ModuleCat.{z} Y)

/- Lemma 18.25.1 (3) (08M3): the essential image consists exactly of module sheaves
annihilated by the kernel of the structure-sheaf map. -/
@[stacks 08M3 "(3)"]
#check
  (mem_essImage_iff_isAnnihilatedByKernel f G :
    f.modulePushforward.{z}.essImage G ↔
      SheafOfModules.IsAnnihilatedByKernel f.structureSheafMap G)

end RingedSite.Hom.ModulePushforward
