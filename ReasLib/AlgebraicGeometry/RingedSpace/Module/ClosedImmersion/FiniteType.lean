/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PushforwardStalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-type modules under a closed embedding

The reusable core separates the two directions. Reflection needs only an inducing underlying
map. Preservation needs a closed embedding and local surjectivity of the structure-sheaf map.
The closed-immersion API is a thin specialization that supplies these hypotheses automatically.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModulePushforward

variable {X Z : RingedSpace.{u}}

namespace Inducing

/-- Finite type of a module pushforward along an inducing ringed-space morphism reflects to the
source module sheaf. No local-surjectivity hypothesis is needed. -/
@[stacks 01C4 "inducing reflection for ringed spaces"]
theorem of_pushforward_isFiniteType
    (i : Z ⟶ X) (hi : Topology.IsInducing i.hom.base)
    (F : Z.Modules) (hF : ((pushforward i).obj F).IsFiniteType) :
    F.IsFiniteType := sorry

end Inducing

namespace ClosedEmbedding

/-- Module pushforward along a closed embedding with locally surjective structure-sheaf map
preserves finite type. -/
@[stacks 01C4 "closed embedding preservation for ringed spaces"]
theorem isFiniteType
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (F : Z.Modules) [F.IsFiniteType] :
    ((pushforward i).obj F).IsFiniteType := sorry

/-- Lemma 17.13.3 (01C4), with the minimal hypotheses: module pushforward along a closed
embedding with locally surjective structure-sheaf map preserves and reflects finite type. -/
@[stacks 01C4]
theorem isFiniteType_iff
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (F : Z.Modules) :
    ((pushforward i).obj F).IsFiniteType ↔ F.IsFiniteType := sorry

end ClosedEmbedding

end AlgebraicGeometry.RingedSpace.Hom.ModulePushforward

namespace AlgebraicGeometry.RingedSpace.IsClosedImmersion

variable {X Z : RingedSpace.{u}}

/-- The closed-immersion specialization of finite-type invariance under module pushforward. -/
@[stacks 01C4 "closed immersion specialization"]
theorem pushforward_isFiniteType_iff
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] (F : Z.Modules) :
    ((pushforward i).obj F).IsFiniteType ↔ F.IsFiniteType := sorry

/-- Pushforward along a closed immersion preserves finite type. -/
instance pushforward_isFiniteType
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (F : Z.Modules) [F.IsFiniteType] :
    ((pushforward i).obj F).IsFiniteType := sorry

/-- Finite type of the pushforward along a closed immersion reflects to the source module
sheaf. -/
theorem of_pushforward_isFiniteType
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (F : Z.Modules) (hF : ((pushforward i).obj F).IsFiniteType) :
    F.IsFiniteType := sorry

variable (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
variable (F : Z.Modules) [F.IsFiniteType]

#synth ((pushforward i).obj F).IsFiniteType

end AlgebraicGeometry.RingedSpace.IsClosedImmersion
